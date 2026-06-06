-- Companion obligations file for the `repeat_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import repeat_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Repeat_usizeObligations

open repeat_usize

/-! ## Helper lemmas ported from the `repeat_packed_usize_modified`,
    `padding_needed_for_usize_modified`, and `is_size_align_valid_usize_modified`
    proof patterns. -/

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_2_63_toNat :
    (9223372036854775808 : usize).toNat = 2 ^ 63 := by decide
private theorem usize_MAX_toNat :
    (18446744073709551615 : usize).toNat = 2 ^ 64 - 1 := by decide

/-- `x ≠ 0` ⟹ `x -? 1 = ok (x - 1)`. -/
private theorem usize_sub_one_ok {x : usize} (hx : x ≠ 0) :
    (x -? (1 : usize)) = RustM.ok (x - 1) := by
  have hno : ¬ (BitVec.usubOverflow x.toBitVec (1#64) = true) := by
    have h0 : (USize64.subOverflow x 1 = true) ↔ x.toNat < (1 : usize).toNat :=
      USize64.subOverflow_iff
    have h1 : (1 : usize).toNat = 1 := rfl
    have hxnz : x.toNat ≠ 0 := by
      intro h; apply hx; apply USize64.toNat_inj.mp; exact h
    show ¬ (USize64.subOverflow x 1 = true)
    rw [h0, h1]; omega
  show (if BitVec.usubOverflow x.toBitVec (1#64) = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure (x - 1)) = RustM.ok (x - 1)
  rw [if_neg hno]; rfl

/-- `max_size_for_align align = ok (2^63 - align)` when `align ≤ 2^63`. -/
private theorem max_size_for_align_ok {align : usize}
    (h : align.toNat ≤ 2 ^ 63) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  have hno :
      ¬ (BitVec.usubOverflow (9223372036854775808 : usize).toBitVec
            align.toBitVec = true) := by
    show ¬ (USize64.subOverflow (9223372036854775808 : usize) align = true)
    rw [USize64.subOverflow_iff, usize_2_63_toNat]; omega
  show (if BitVec.usubOverflow (9223372036854775808 : usize).toBitVec
            align.toBitVec = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure ((9223372036854775808 : usize) - align))
      = RustM.ok ((9223372036854775808 : usize) - align)
  rw [if_neg hno]; rfl

private theorem max_size_for_align_toNat {align : usize}
    (h : align.toNat ≤ 2 ^ 63) :
    ((9223372036854775808 : usize) - align).toNat = 2 ^ 63 - align.toNat := by
  have h_le : align.toNat ≤ (9223372036854775808 : usize).toNat := by
    rw [usize_2_63_toNat]; exact h
  rw [USize64.toNat_sub_of_le' h_le, usize_2_63_toNat]

/-- `size.toNat + align.toNat ≤ 2^63` ⟹ `from_size_alignment size align = ok (Ok ⟨size, align⟩)`. -/
private theorem from_size_alignment_ok {size align : usize}
    (h : size.toNat + align.toNat ≤ 2 ^ 63) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := size) (align := align))) := by
  have halign : align.toNat ≤ 2 ^ 63 := by omega
  have hMax := max_size_for_align_ok halign
  have hSubToNat := max_size_for_align_toNat halign
  have hNotGt : ¬ ((9223372036854775808 : usize) - align) < size := by
    rw [USize64.lt_iff_toNat_lt, hSubToNat]; omega
  unfold from_size_alignment
  show (do
      let __do_lift ← max_size_for_align align
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = _
  rw [hMax]
  show (do
      let __do_lift ← (pure ((9223372036854775808 : usize) - align) : RustM usize)
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = _
  simp only [pure_bind]
  show (do
      let __do_lift ← (pure (decide (size > ((9223372036854775808 : usize) - align))) : RustM Bool)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = _
  simp only [pure_bind]
  have : decide (size > ((9223372036854775808 : usize) - align)) = false := by
    apply decide_eq_false; intro h_gt; exact hNotGt h_gt
  rw [this]; rfl

private theorem from_size_alignment_err {size align : usize}
    (halign : align.toNat ≤ 2 ^ 63)
    (hsz : 2 ^ 63 < size.toNat + align.toNat) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hMax := max_size_for_align_ok halign
  have hSubToNat := max_size_for_align_toNat halign
  have hGt : ((9223372036854775808 : usize) - align) < size := by
    rw [USize64.lt_iff_toNat_lt, hSubToNat]; omega
  unfold from_size_alignment
  show (do
      let __do_lift ← max_size_for_align align
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = _
  rw [hMax]
  show (do
      let __do_lift ← (pure ((9223372036854775808 : usize) - align) : RustM usize)
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = _
  simp only [pure_bind]
  show (do
      let __do_lift ← (pure (decide (size > ((9223372036854775808 : usize) - align))) : RustM Bool)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = _
  simp only [pure_bind]
  rw [decide_eq_true (show size > ((9223372036854775808 : usize) - align) from hGt)]
  rfl

/-! ## Bit-trick lemmas for the power-of-two alignment rounding. -/

private theorem usize_pow_of_two_le {x : usize}
    (hnz : x ≠ 0) (hand : x &&& (x - 1) = 0) :
    x.toNat ≤ 2 ^ 63 := by
  have hbv : x.toBitVec ≠ 0#64 := by
    intro h; apply hnz; apply USize64.toBitVec_inj.mp; exact h
  have hbvand : x.toBitVec &&& (x.toBitVec - 1#64) = 0#64 := by
    have h1 : (x &&& (x - 1)).toBitVec = x.toBitVec &&& (x - 1).toBitVec := rfl
    have h2 : (x - 1).toBitVec = x.toBitVec - 1#64 := rfl
    have h3 : (0 : usize).toBitVec = 0#64 := rfl
    have h4 : (x &&& (x - 1)).toBitVec = (0 : usize).toBitVec := by rw [hand]
    rw [h1, h2] at h4; rw [h4, h3]
  show x.toBitVec.toNat ≤ 2 ^ 63
  have hbv_le : x.toBitVec ≤ 0x8000000000000000#64 := by
    revert hbv hbvand; bv_decide
  have hnat_le : x.toBitVec.toNat ≤ (0x8000000000000000#64).toNat :=
    BitVec.le_def.mp hbv_le
  have hb : (0x8000000000000000#64).toNat = 2 ^ 63 := by decide
  omega

/-- Key BV lemma: for any `s, a` with `a ≠ 0`, `a &&& (a-1) = 0`, and
    `s + (a-1)` not overflowing, the bit-trick rounded value is between
    `s` and `s + a`, with low bits cleared. -/
private theorem bv_padding_key (s a : BitVec 64)
    (hnz : a ≠ 0#64)
    (hand : a &&& (a - 1#64) = 0#64)
    (hovf : BitVec.uaddOverflow s (a - 1#64) = false) :
    s ≤ ((s + (a - 1#64)) &&& ~~~(a - 1#64))
    ∧ ((s + (a - 1#64)) &&& ~~~(a - 1#64)) &&& (a - 1#64) = 0#64
    ∧ ((s + (a - 1#64)) &&& ~~~(a - 1#64)) - s < a := by
  bv_decide

/-- `x &&& (a - 1) = x % a` for power-of-two `a`. -/
private theorem bv_and_mask_eq_mod (x a : BitVec 64)
    (hnz : a ≠ 0#64)
    (hand : a &&& (a - 1#64) = 0#64) :
    x &&& (a - 1#64) = x % a := by
  bv_decide (config := {timeout := 120})

@[simp] private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- Closed-form for `size_rounded_up_to_custom_align`. -/
private theorem size_rounded_up_compute (size align : usize)
    (hnz : align ≠ 0)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    size_rounded_up_to_custom_align size align
      = RustM.ok ((size + (align - 1)) &&& ~~~ (align - 1)) := by
  have hnz_n : align.toNat ≠ 0 := fun h => hnz (USize64.toNat_inj.mp h)
  have halign_pos : 1 ≤ align.toNat := by omega
  have h_align_sub_one : align -? (1 : usize) = RustM.ok (align - 1) :=
    usize_sub_one_ok hnz
  have h_align_m1_nat : (align - 1).toNat = align.toNat - 1 := by
    have h := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ align.toNat by
      rw [usize_one_toNat]; exact halign_pos)
    rw [usize_one_toNat] at h; exact h
  have h_add_ok_nat : size.toNat + (align - 1).toNat < 2 ^ 64 := by
    rw [h_align_m1_nat]; omega
  have h_no_ovf_add :
      BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : USize64.addOverflow size (align - 1) = true := h_eq
      rw [USize64.addOverflow_iff] at this; omega
  have h_size_add : (size +? (align - 1) : RustM usize)
                      = RustM.ok (size + (align - 1)) := by
    show (if BitVec.uaddOverflow size.toBitVec (align - 1).toBitVec = true then
            (RustM.fail .integerOverflow : RustM usize)
          else pure (size + (align - 1))) = RustM.ok (size + (align - 1))
    rw [if_neg (by rw [h_no_ovf_add]; decide)]; rfl
  unfold size_rounded_up_to_custom_align
  rw [h_align_sub_one, RustM_ok_bind, h_size_add, RustM_ok_bind]
  rfl

/-- Closed-form for `pad_to_align`: returns `{ size := rounded, align := layout.align }`. -/
private theorem pad_to_align_ok (layout : Layout)
    (hnz : layout.align ≠ 0)
    (hbound : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64) :
    pad_to_align layout
      = RustM.ok
          (Layout.mk
            (size := (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1))
            (align := layout.align)) := by
  unfold pad_to_align
  rw [size_rounded_up_compute layout.size layout.align hnz hbound, RustM_ok_bind]
  rfl

/-- `repeat_packed` ok-branch (ported from `repeat_packed_usize_modified`).
    When `layout.size * n + layout.align ≤ 2^63`, returns
    `Ok ⟨layout.size * n, layout.align⟩`. -/
private theorem repeat_packed_ok (layout : Layout) (n : usize)
    (hbnd : layout.size.toNat * n.toNat + layout.align.toNat ≤ 2 ^ 63) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Ok
        (Layout.mk (size := layout.size * n) (align := layout.align))) := by
  unfold repeat_packed
  by_cases hn : n = 0
  · subst hn
    show (do
        let __do_lift ← ((0 : usize) ==? (0 : usize) : RustM Bool)
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else
          do
            let __do_lift ← ((18446744073709551615 : usize) /? (0 : usize))
            let __do_lift ← (Layout.size layout >? __do_lift)
            if __do_lift = true then
              pure (core_models.result.Result.Err LayoutError.mk)
            else
              do
                let __do_lift ← (Layout.size layout *? (0 : usize))
                from_size_alignment __do_lift (Layout.align layout))
      = _
    show (do
        let __do_lift ← (pure ((0 : usize) == (0 : usize)) : RustM Bool)
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else _) = _
    have h_beq : ((0 : usize) == (0 : usize)) = true := by decide
    rw [h_beq]
    simp only [pure_bind, if_true]
    have h_mul_zero : layout.size * (0 : usize) = (0 : usize) := USize64.mul_zero
    rw [h_mul_zero]
    have hbnd' : (0 : usize).toNat + (Layout.align layout).toNat ≤ 2 ^ 63 := by
      rw [usize_zero_toNat]; omega
    exact from_size_alignment_ok hbnd'
  · have h_eq_decide : decide ((n : usize) = (0 : usize)) = false :=
      decide_eq_false hn
    have hsn_bound : layout.size.toNat * n.toNat ≤ 2 ^ 63 := by omega
    have hsn_lt : layout.size.toNat * n.toNat < 2 ^ 64 := by
      have hpow : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
      omega
    have h_nomul : ¬ USize64.mulOverflow layout.size n := by
      rw [USize64.mulOverflow_iff]; omega
    have h_nomul_bv :
        BitVec.umulOverflow layout.size.toBitVec n.toBitVec = false := by
      cases h_eq : BitVec.umulOverflow layout.size.toBitVec n.toBitVec with
      | false => rfl
      | true => exact absurd h_eq h_nomul
    have h_mul_toNat : (layout.size * n).toNat
                        = layout.size.toNat * n.toNat :=
      USize64.toNat_mul_of_lt hsn_lt
    have hn_pos : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
      · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
      · exact hpos
    have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                  = pure ((18446744073709551615 : usize) / n) := by
      show (if n = 0 then (.fail .divisionByZero : RustM usize)
            else pure ((18446744073709551615 : usize) / n)) = _
      rw [if_neg hn]
    have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                        = (2 ^ 64 - 1) / n.toNat := by
      rw [USize64.toNat_div, usize_MAX_toNat]
    have h_not_gt : ¬ ((18446744073709551615 : usize) / n) < layout.size := by
      rw [USize64.lt_iff_toNat_lt, h_div_toNat]
      have h_le : layout.size.toNat * n.toNat ≤ 2 ^ 64 - 1 := by
        have hpow : (2 : Nat) ^ 63 ≤ 2 ^ 64 - 1 := by decide
        omega
      have h := (Nat.le_div_iff_mul_le hn_pos).mpr h_le
      omega
    have h_mul : (layout.size *? n : RustM usize)
                  = pure (layout.size * n) := by
      show (if BitVec.umulOverflow layout.size.toBitVec n.toBitVec = true then
              (.fail .integerOverflow : RustM usize)
            else pure (layout.size * n)) = _
      rw [if_neg (by rw [h_nomul_bv]; decide)]
    have h_bnd' : (layout.size * n).toNat + layout.align.toNat ≤ 2 ^ 63 := by
      rw [h_mul_toNat]; exact hbnd
    have h_fsa := from_size_alignment_ok h_bnd'
    show (do
        let __do_lift ← (pure ((n : usize) == (0 : usize)) : RustM Bool)
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else _) = _
    simp only [pure_bind]
    have h_beq_false : ((n : usize) == (0 : usize)) = false := by
      rw [show ((n : usize) == (0 : usize)) = decide ((n : usize) = (0 : usize)) from rfl]
      exact h_eq_decide
    rw [h_beq_false]
    simp only [Bool.false_eq_true, if_false]
    rw [h_div]; simp only [pure_bind]
    show (do
        let __do_lift ← (pure (decide (Layout.size layout > (18446744073709551615 : usize) / n)) : RustM Bool)
        if __do_lift = true then
          pure (core_models.result.Result.Err LayoutError.mk)
        else
          do
            let __do_lift ← (Layout.size layout *? n)
            from_size_alignment __do_lift (Layout.align layout))
      = _
    simp only [pure_bind]
    have h_dec_false :
        decide (Layout.size layout > (18446744073709551615 : usize) / n) = false := by
      apply decide_eq_false; intro h_gt; exact h_not_gt h_gt
    rw [h_dec_false]
    simp only [Bool.false_eq_true, if_false]
    rw [h_mul]; simp only [pure_bind]
    exact h_fsa

/-- `repeat_packed` err-branch (size too large, fits in usize). -/
private theorem repeat_packed_err_size_too_large (layout : Layout) (n : usize)
    (hn : n ≠ 0)
    (hnomul : layout.size.toNat * n.toNat < 2 ^ 64)
    (halign : layout.align.toNat ≤ 2 ^ 63)
    (hsz : 2 ^ 63 < layout.size.toNat * n.toNat + layout.align.toNat) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  unfold repeat_packed
  have h_eq_decide : decide ((n : usize) = (0 : usize)) = false :=
    decide_eq_false hn
  have h_nomul : ¬ USize64.mulOverflow layout.size n := by
    rw [USize64.mulOverflow_iff]; omega
  have h_nomul_bv :
      BitVec.umulOverflow layout.size.toBitVec n.toBitVec = false := by
    cases h_eq : BitVec.umulOverflow layout.size.toBitVec n.toBitVec with
    | false => rfl
    | true => exact absurd h_eq h_nomul
  have h_mul_toNat : (layout.size * n).toNat = layout.size.toNat * n.toNat :=
    USize64.toNat_mul_of_lt hnomul
  have hn_pos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
    · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
    · exact hpos
  have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                = pure ((18446744073709551615 : usize) / n) := by
    show (if n = 0 then (.fail .divisionByZero : RustM usize)
          else pure ((18446744073709551615 : usize) / n)) = _
    rw [if_neg hn]
  have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                      = (2 ^ 64 - 1) / n.toNat := by
    rw [USize64.toNat_div, usize_MAX_toNat]
  have h_not_gt : ¬ ((18446744073709551615 : usize) / n) < layout.size := by
    rw [USize64.lt_iff_toNat_lt, h_div_toNat]
    have h_le : layout.size.toNat * n.toNat ≤ 2 ^ 64 - 1 := by omega
    have h := (Nat.le_div_iff_mul_le hn_pos).mpr h_le; omega
  have h_mul : (layout.size *? n : RustM usize) = pure (layout.size * n) := by
    show (if BitVec.umulOverflow layout.size.toBitVec n.toBitVec = true then
            (.fail .integerOverflow : RustM usize)
          else pure (layout.size * n)) = _
    rw [if_neg (by rw [h_nomul_bv]; decide)]
  have h_sum : 2 ^ 63 < (layout.size * n).toNat + layout.align.toNat := by
    rw [h_mul_toNat]; exact hsz
  have h_fsa := from_size_alignment_err halign h_sum
  show (do
      let __do_lift ← (pure ((n : usize) == (0 : usize)) : RustM Bool)
      if __do_lift = true then
        from_size_alignment (0 : usize) (Layout.align layout)
      else _) = _
  simp only [pure_bind]
  have h_beq_false : ((n : usize) == (0 : usize)) = false := by
    rw [show ((n : usize) == (0 : usize)) = decide ((n : usize) = (0 : usize)) from rfl]
    exact h_eq_decide
  rw [h_beq_false]
  simp only [Bool.false_eq_true, if_false]
  rw [h_div]; simp only [pure_bind]
  show (do
      let __do_lift ← (pure (decide (Layout.size layout > (18446744073709551615 : usize) / n)) : RustM Bool)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        do
          let __do_lift ← (Layout.size layout *? n)
          from_size_alignment __do_lift (Layout.align layout))
    = _
  simp only [pure_bind]
  have h_dec_false :
      decide (Layout.size layout > (18446744073709551615 : usize) / n) = false := by
    apply decide_eq_false; intro h_gt; exact h_not_gt h_gt
  rw [h_dec_false]
  simp only [Bool.false_eq_true, if_false]
  rw [h_mul]; simp only [pure_bind]
  exact h_fsa

/-- Bind reduction (Option-Except form): `(x >>= f) = RustM.ok v` iff there is
    an intermediate `a` with `x = RustM.ok a` and `f a = RustM.ok v`. -/
private theorem RustM_bind_eq_ok_iff {α β : Type} (x : RustM α) (f : α → RustM β) (v : β) :
    (x >>= f) = RustM.ok v ↔ ∃ a, x = RustM.ok a ∧ f a = RustM.ok v := by
  constructor
  · intro h
    -- `match` substitutes x in h directly.
    match h_x : x, h with
    | none, h =>
        exfalso
        -- h : (none >>= f) = RustM.ok v.  Bind of none reduces to none.
        exact (by cases h)
    | some (Except.error e), h =>
        exfalso
        -- h : (some (Except.error e) >>= f) = RustM.ok v reduces to ≠.
        exact (by cases h)
    | some (Except.ok a), h =>
        -- After match: x is substituted to `some (Except.ok a)` in the goal.
        -- The existential goal becomes `∃ a', some (.ok a) = RustM.ok a' ∧ …`.
        -- Choose a' = a (rfl for first conjunct since RustM.ok a ≡ some (.ok a)).
        exact ⟨a, rfl, h⟩
  · rintro ⟨a, ha, hfa⟩
    rw [ha]; exact hfa

/-- From a successful pad_to_align, recover: align ≠ 0, size + align ≤ 2^64,
    and padded has the closed-form bit-trick size and the input alignment. -/
private theorem pad_to_align_ok_inv {layout padded : Layout}
    (h : pad_to_align layout = RustM.ok padded) :
    layout.align ≠ 0 ∧ layout.size.toNat + layout.align.toNat ≤ 2 ^ 64 ∧
    padded = Layout.mk
      (size := (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1))
      (align := layout.align) := by
  -- Unfold pad_to_align as a bind.
  have hpd : pad_to_align layout =
      (size_rounded_up_to_custom_align layout.size layout.align >>=
        fun new_size => (pure (Layout.mk new_size layout.align) : RustM Layout)) := rfl
  rw [hpd] at h
  obtain ⟨new_size, hsrucl, hpure⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h
  -- hpure : pure (Layout.mk new_size layout.align) = ok padded
  have hpadded : padded = Layout.mk new_size layout.align := by
    injection hpure with h_ex
    injection h_ex with h_eq
    exact h_eq.symm
  -- Now invert srucl.
  have hsrucl_unfold : size_rounded_up_to_custom_align layout.size layout.align =
      ((layout.align -? (1 : usize)) >>= fun align_m1 =>
        ((layout.size +? align_m1) >>= fun s_plus =>
          ((~? align_m1) >>= fun nm =>
            ((s_plus &&&? nm) : RustM usize)))) := rfl
  rw [hsrucl_unfold] at hsrucl
  obtain ⟨align_m1, h_am1, h_rest⟩ := (RustM_bind_eq_ok_iff _ _ _).mp hsrucl
  -- align ≠ 0 from h_am1
  have hnz : layout.align ≠ 0 := by
    intro h_eq
    rw [h_eq] at h_am1
    have h_ov : BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec = true := by decide
    have hzero_sub :
        ((0 : usize) -? (1 : usize) : RustM usize) = RustM.fail .integerOverflow := by
      show (if BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec = true then
              (RustM.fail .integerOverflow : RustM usize)
            else pure ((0 : usize) - (1 : usize))) = RustM.fail .integerOverflow
      rw [if_pos h_ov]
    rw [hzero_sub] at h_am1; cases h_am1
  have h_am1_eq : align_m1 = layout.align - 1 := by
    have huo := usize_sub_one_ok hnz
    rw [huo] at h_am1
    injection h_am1 with h_ex
    injection h_ex with h_eq
    exact h_eq.symm
  subst h_am1_eq
  obtain ⟨s_plus, h_sp, h_rest2⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h_rest
  -- Derive hadd: size + align ≤ 2^64
  have hnz_n : layout.align.toNat ≠ 0 := fun heq => hnz (USize64.toNat_inj.mp heq)
  have h_am1_nat : (layout.align - 1).toNat = layout.align.toNat - 1 := by
    have htn := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ layout.align.toNat by
      rw [usize_one_toNat]; omega)
    rw [usize_one_toNat] at htn; exact htn
  -- Derive: no overflow in (size + (align - 1)), hence size + align ≤ 2^64.
  have h_no_ov :
      BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have hfail :
          (layout.size +? (layout.align - 1) : RustM usize)
            = RustM.fail .integerOverflow := by
        show (if BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec = true
              then (RustM.fail .integerOverflow : RustM usize)
              else pure (layout.size + (layout.align - 1))) = _
        rw [if_pos h_eq]
      rw [hfail] at h_sp; cases h_sp
  have h_not_ge : ¬ (layout.size.toNat + (layout.align - 1).toNat ≥ 2 ^ 64) := by
    intro h_ge
    have := (USize64.uaddOverflow_iff layout.size (layout.align - 1)).mpr h_ge
    rw [h_no_ov] at this; cases this
  have h_add_lt : layout.size.toNat + (layout.align - 1).toNat < 2 ^ 64 :=
    Nat.lt_of_not_le h_not_ge
  have hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64 := by
    rw [h_am1_nat] at h_add_lt; omega
  have h_sp_compute :
      (layout.size +? (layout.align - 1) : RustM usize)
        = RustM.ok (layout.size + (layout.align - 1)) := by
    show (if BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec = true then
            (RustM.fail .integerOverflow : RustM usize)
          else pure (layout.size + (layout.align - 1))) = _
    rw [if_neg (by rw [h_no_ov]; decide)]
    rfl
  rw [h_sp_compute] at h_sp
  have h_sp_eq : s_plus = layout.size + (layout.align - 1) := by
    injection h_sp with h_ex
    injection h_ex with h_eq
    exact h_eq.symm
  subst h_sp_eq
  -- ~? always returns RustM.ok (~~~ ...).  Reduce h_rest2 by rfl.
  -- h_rest2 already beta-reduces to: pure (... &&& ...) = RustM.ok new_size.
  have h_ns_eq :
      new_size = (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1) := by
    injection h_rest2 with h_ex
    injection h_ex with h_eq
    exact h_eq.symm
  subst h_ns_eq
  exact ⟨hnz, hadd, hpadded⟩

/-- From an Ok result of `repeat_layout`, recover: pad_to_align succeeded
    (with some padded), repeat_packed succeeded with `Ok arr`, and the stride
    `offs` is `padded.size`. -/
private theorem repeat_layout_ok_inv (layout : Layout) (n : usize)
    (arr : Layout) (offs : usize)
    (h : repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    ∃ padded : Layout,
      pad_to_align layout = RustM.ok padded
      ∧ repeat_packed padded n
          = RustM.ok (core_models.result.Result.Ok arr)
      ∧ offs = padded.size := by
  have hunfold : repeat_layout layout n = (pad_to_align layout >>= fun padded =>
      repeat_packed padded n >>= fun rp =>
        match rp with
        | core_models.result.Result.Ok repeated =>
            Impl.size padded >>= fun s =>
              pure (core_models.result.Result.Ok
                (rust_primitives.hax.Tuple2.mk repeated s))
        | _ => pure (core_models.result.Result.Err LayoutError.mk)) := rfl
  rw [hunfold] at h
  obtain ⟨padded, hpta, h1⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h
  refine ⟨padded, hpta, ?_, ?_⟩
  · obtain ⟨rp, hrp, h2⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h1
    cases rp with
    | Err _ =>
        exfalso
        change (some (Except.ok (core_models.result.Result.Err LayoutError.mk)) :
                  RustM (core_models.result.Result _ _))
            = some (Except.ok (core_models.result.Result.Ok _)) at h2
        cases h2
    | Ok repeated =>
        -- h2: (Impl.size padded >>= …) = ok (Ok (Tuple2.mk arr offs))
        obtain ⟨s, hs, h3⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h2
        have hs' : s = padded.size := by
          have hisz : Impl.size padded = RustM.ok padded.size := rfl
          rw [hisz] at hs
          injection hs with h_ex
          injection h_ex with h_eq
          exact h_eq.symm
        subst hs'
        -- h3 : pure (Result.Ok (Tuple2.mk repeated padded.size))
        --     = RustM.ok (Result.Ok (Tuple2.mk arr offs))
        injection h3 with h_ex
        injection h_ex with h_inj
        injection h_inj with h_tup
        -- h_tup : repeated = arr (the first Tuple2 component)
        -- Actually, injection on the Tuple2 may give both components.
        -- Let's extract via Tuple2.mk.injEq:
        have h_inj' :=
          rust_primitives.hax.Tuple2.mk.injEq repeated padded.size arr offs |>.mp h_tup
        rw [hrp, h_inj'.1]
  · obtain ⟨rp, hrp, h2⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h1
    cases rp with
    | Err _ =>
        exfalso
        change (some (Except.ok (core_models.result.Result.Err LayoutError.mk)) :
                  RustM (core_models.result.Result _ _))
            = some (Except.ok (core_models.result.Result.Ok _)) at h2
        cases h2
    | Ok repeated =>
        obtain ⟨s, hs, h3⟩ := (RustM_bind_eq_ok_iff _ _ _).mp h2
        have hs' : s = padded.size := by
          have hisz : Impl.size padded = RustM.ok padded.size := rfl
          rw [hisz] at hs
          injection hs with h_ex
          injection h_ex with h_eq
          exact h_eq.symm
        subst hs'
        injection h3 with h_ex
        injection h_ex with h_inj
        injection h_inj with h_tup
        have h_inj' :=
          rust_primitives.hax.Tuple2.mk.injEq repeated padded.size arr offs |>.mp h_tup
        exact h_inj'.2.symm

/-- Inversion of `from_size_alignment`: if it returns `Ok arr`, then
    `arr = Layout.mk size align`. -/
private theorem from_size_alignment_ok_inv {size align : usize} {arr : Layout}
    (h : from_size_alignment size align
          = RustM.ok (core_models.result.Result.Ok arr)) :
    arr = Layout.mk (size := size) (align := align) := by
  unfold from_size_alignment at h
  -- h : (do let __ ← max_size_for_align align;
  --         let __ ← (size >? __);
  --         if __ then pure (Err) else pure (Ok (Layout.mk size align)))
  --   = RustM.ok (Ok arr)
  -- Case-split on `max_size_for_align align`.
  cases hmax : max_size_for_align align with
  | none =>
      exfalso
      rw [hmax] at h
      cases h
  | some mres =>
    cases mres with
    | error e =>
        exfalso
        rw [hmax] at h
        cases h
    | ok mx =>
        rw [hmax] at h
        -- h : (do let __ ← (size >? mx); ...) = ok (Ok arr)
        change ((size >? mx : RustM Bool) >>= fun __do_lift =>
          if __do_lift = true then
            (pure (core_models.result.Result.Err LayoutError.mk) : RustM _)
          else
            pure (core_models.result.Result.Ok
              (Layout.mk (size := size) (align := align))))
            = RustM.ok (core_models.result.Result.Ok arr) at h
        -- (size >? mx) = pure (decide (size > mx)) = RustM.ok ...
        have hcmp : (size >? mx : RustM Bool)
                    = RustM.ok (decide (size > mx)) := rfl
        rw [hcmp, RustM_ok_bind] at h
        -- h : (if decide(size > mx) then ... Err else Ok (Layout.mk size align))
        --     = ok (Ok arr)
        cases hb : decide (size > mx) with
        | true =>
            exfalso
            rw [hb] at h
            simp only [if_pos rfl] at h
            injection h with h_ex
            injection h_ex with h_eq
            cases h_eq
        | false =>
            rw [hb] at h
            simp only [Bool.false_eq_true, if_false] at h
            injection h with h_ex
            injection h_ex with h_eq
            injection h_eq with h_arr
            exact h_arr.symm

/-- Inversion of `repeat_packed`: if it returns `Ok arr`, then
    `arr = Layout.mk (layout.size * n) layout.align`. -/
private theorem repeat_packed_ok_inv {layout : Layout} {n : usize} {arr : Layout}
    (h : repeat_packed layout n
          = RustM.ok (core_models.result.Result.Ok arr)) :
    arr = Layout.mk (size := layout.size * n) (align := layout.align) := by
  unfold repeat_packed at h
  by_cases hn : n = 0
  · subst hn
    have h_beq : ((0 : usize) ==? (0 : usize) : RustM Bool) = RustM.ok true := rfl
    -- h : (do let __ ← (0 ==? 0); if __ then from_size_alignment 0 align else ...) = ok (Ok arr)
    change ((((0 : usize) ==? (0 : usize)) : RustM Bool) >>= fun __do_lift =>
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else
          ((((18446744073709551615 : usize) /? (0 : usize)) : RustM usize) >>= fun __do_lift =>
            ((Layout.size layout >? __do_lift) : RustM Bool) >>= fun __do_lift =>
              if __do_lift = true then
                (pure (core_models.result.Result.Err LayoutError.mk) : RustM _)
              else
                (((Layout.size layout *? (0 : usize)) : RustM usize) >>= fun __do_lift =>
                  from_size_alignment __do_lift (Layout.align layout))))
        = RustM.ok (core_models.result.Result.Ok arr) at h
    rw [h_beq, RustM_ok_bind] at h
    simp only [if_pos rfl] at h
    -- h : from_size_alignment 0 align = ok (Ok arr)
    have h_arr := from_size_alignment_ok_inv h
    rw [h_arr, USize64.mul_zero]
  · have h_beq : ((n : usize) ==? (0 : usize) : RustM Bool)
                  = RustM.ok (decide (n = 0)) := rfl
    change ((((n : usize) ==? (0 : usize)) : RustM Bool) >>= fun __do_lift =>
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else
          ((((18446744073709551615 : usize) /? n) : RustM usize) >>= fun __do_lift =>
            ((Layout.size layout >? __do_lift) : RustM Bool) >>= fun __do_lift =>
              if __do_lift = true then
                (pure (core_models.result.Result.Err LayoutError.mk) : RustM _)
              else
                (((Layout.size layout *? n) : RustM usize) >>= fun __do_lift =>
                  from_size_alignment __do_lift (Layout.align layout))))
        = RustM.ok (core_models.result.Result.Ok arr) at h
    rw [h_beq, RustM_ok_bind] at h
    rw [decide_eq_false hn] at h
    simp only [Bool.false_eq_true, if_false] at h
    -- h : (do let __ ← MAX /? n; ...) = ok (Ok arr)
    have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                  = pure ((18446744073709551615 : usize) / n) := by
      show (if n = 0 then (.fail .divisionByZero : RustM usize)
            else pure ((18446744073709551615 : usize) / n)) = _
      rw [if_neg hn]
    rw [h_div, pure_bind] at h
    -- h : (do let __ ← (size >? MAX/n); ...) = ok (Ok arr)
    have h_cmp : (layout.size >? ((18446744073709551615 : usize) / n) : RustM Bool)
                  = RustM.ok (decide (layout.size > (18446744073709551615 : usize) / n)) := rfl
    rw [h_cmp, RustM_ok_bind] at h
    cases hb : decide (layout.size > (18446744073709551615 : usize) / n) with
    | true =>
        exfalso
        rw [hb] at h
        simp only [if_pos rfl] at h
        injection h with h_ex
        injection h_ex with h_eq
        cases h_eq
    | false =>
        rw [hb] at h
        simp only [Bool.false_eq_true, if_false] at h
        -- h : (do let __ ← size *? n; from_size_alignment __ align) = ok (Ok arr)
        -- size *? n succeeds because if it overflowed, MAX/n < size, but hb says ¬.
        have h_not_gt : ¬ ((18446744073709551615 : usize) / n) < layout.size := by
          intro h_gt; exact absurd (decide_eq_true h_gt) (by rw [hb]; decide)
        have hn_pos : 0 < n.toNat := by
          rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
          · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
          · exact hpos
        -- size.toNat ≤ MAX/n.toNat ≤ ... → size.toNat * n.toNat ≤ 2^64 - 1 < 2^64
        have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                          = (2 ^ 64 - 1) / n.toNat := by
          rw [USize64.toNat_div, usize_MAX_toNat]
        have h_size_le : layout.size.toNat ≤ (2 ^ 64 - 1) / n.toNat := by
          have h1 : ¬ ((18446744073709551615 : usize) / n).toNat < layout.size.toNat := by
            rw [USize64.lt_iff_toNat_lt] at h_not_gt; exact h_not_gt
          rw [h_div_toNat] at h1; omega
        have h_mul_le : layout.size.toNat * n.toNat ≤ 2 ^ 64 - 1 := by
          calc layout.size.toNat * n.toNat
              ≤ ((2 ^ 64 - 1) / n.toNat) * n.toNat := by
                exact Nat.mul_le_mul_right _ h_size_le
            _ ≤ 2 ^ 64 - 1 := Nat.div_mul_le_self _ _
        have h_mul_lt : layout.size.toNat * n.toNat < 2 ^ 64 := by omega
        have h_nomul_bv :
            BitVec.umulOverflow layout.size.toBitVec n.toBitVec = false := by
          cases h_eq : BitVec.umulOverflow layout.size.toBitVec n.toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : USize64.mulOverflow layout.size n = true := h_eq
            rw [USize64.mulOverflow_iff] at this
            omega
        have h_mul : (layout.size *? n : RustM usize)
                      = pure (layout.size * n) := by
          show (if BitVec.umulOverflow layout.size.toBitVec n.toBitVec = true then
                  (.fail .integerOverflow : RustM usize)
                else pure (layout.size * n)) = _
          rw [if_neg (by rw [h_nomul_bv]; decide)]
        rw [h_mul, pure_bind] at h
        exact from_size_alignment_ok_inv h

/-- Compose `pad_to_align` and `repeat_packed` (Ok branch) into a `repeat_layout` result. -/
private theorem repeat_layout_ok_of_helpers
    (layout : Layout) (n : usize) (padded : Layout) (arr : Layout)
    (hpta : pad_to_align layout = RustM.ok padded)
    (hok : repeat_packed padded n
            = RustM.ok (core_models.result.Result.Ok arr)) :
    repeat_layout layout n
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk arr padded.size)) := by
  show (do
      let padded ← pad_to_align layout
      match (← repeat_packed padded n) with
      | core_models.result.Result.Ok repeated => do
        (pure (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk repeated (← (Impl.size padded)))))
      | _ => do (pure (core_models.result.Result.Err LayoutError.mk)))
    = RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr padded.size))
  rw [hpta]; simp only [RustM_ok_bind]
  rw [hok]; simp only [RustM_ok_bind]
  rfl

/-- Compose `pad_to_align` and `repeat_packed` (Err branch) into a `repeat_layout` err. -/
private theorem repeat_layout_err_of_helpers
    (layout : Layout) (n : usize) (padded : Layout)
    (hpta : pad_to_align layout = RustM.ok padded)
    (herr : repeat_packed padded n
            = RustM.ok (core_models.result.Result.Err LayoutError.mk)) :
    repeat_layout layout n
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  show (do
      let padded ← pad_to_align layout
      match (← repeat_packed padded n) with
      | core_models.result.Result.Ok repeated => do
        (pure (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk repeated (← (Impl.size padded)))))
      | _ => do (pure (core_models.result.Result.Err LayoutError.mk)))
    = RustM.ok (core_models.result.Result.Err LayoutError.mk)
  rw [hpta]; simp only [RustM_ok_bind]
  rw [herr]; simp only [RustM_ok_bind]
  rfl

/-- `repeat_packed` err-branch (mul overflows). -/
private theorem repeat_packed_err_mul_overflow (layout : Layout) (n : usize)
    (hov : 2 ^ 64 ≤ layout.size.toNat * n.toNat) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  unfold repeat_packed
  have hn : n ≠ 0 := by
    intro h_eq
    have h_n_zero : n.toNat = 0 := by rw [h_eq]; rfl
    rw [h_n_zero, Nat.mul_zero] at hov
    exact absurd hov (by decide)
  have h_eq_decide : decide ((n : usize) = (0 : usize)) = false :=
    decide_eq_false hn
  have hn_pos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
    · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
    · exact hpos
  have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                = pure ((18446744073709551615 : usize) / n) := by
    show (if n = 0 then (.fail .divisionByZero : RustM usize)
          else pure ((18446744073709551615 : usize) / n)) = _
    rw [if_neg hn]
  have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                      = (2 ^ 64 - 1) / n.toNat := by
    rw [USize64.toNat_div, usize_MAX_toNat]
  have h_gt : ((18446744073709551615 : usize) / n) < layout.size := by
    rw [USize64.lt_iff_toNat_lt, h_div_toNat]
    have h_qn : ((2 ^ 64 - 1) / n.toNat) * n.toNat ≤ 2 ^ 64 - 1 :=
      Nat.div_mul_le_self _ _
    have h_lt :
        ((2 ^ 64 - 1) / n.toNat) * n.toNat < layout.size.toNat * n.toNat := by omega
    exact Nat.lt_of_mul_lt_mul_right h_lt
  show (do
      let __do_lift ← (pure ((n : usize) == (0 : usize)) : RustM Bool)
      if __do_lift = true then
        from_size_alignment (0 : usize) (Layout.align layout)
      else _) = _
  simp only [pure_bind]
  have h_beq_false : ((n : usize) == (0 : usize)) = false := by
    rw [show ((n : usize) == (0 : usize)) = decide ((n : usize) = (0 : usize)) from rfl]
    exact h_eq_decide
  rw [h_beq_false]
  simp only [Bool.false_eq_true, if_false]
  rw [h_div]; simp only [pure_bind]
  show (do
      let __do_lift ← (pure (decide (Layout.size layout > (18446744073709551615 : usize) / n)) : RustM Bool)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        do
          let __do_lift ← (Layout.size layout *? n)
          from_size_alignment __do_lift (Layout.align layout))
    = _
  simp only [pure_bind]
  rw [decide_eq_true (show Layout.size layout > (18446744073709551615 : usize) / n from h_gt)]
  rfl

/-! ## Doc-example anchors

    These pin the concrete outputs the Rust doc-test for `Layout::repeat`
    asserts (transferred verbatim into the `doc_example` test). Decidable on
    closed `usize` arithmetic. -/

/-- `repeat({size:=12, align:=4}, 3) = Ok (Tuple2.mk {size:=36, align:=4} 12)`. -/
theorem repeat_layout_doc_example_1 :
    repeat_layout ⟨(12 : usize), (4 : usize)⟩ (3 : usize) =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk
          ⟨(36 : usize), (4 : usize)⟩ (12 : usize))) := by
  rfl

/-- `repeat({size:=6, align:=4}, 3) = Ok (Tuple2.mk {size:=24, align:=4} 8)`.
    Shows the round-up: stride = 8 (= round-up of 6 to align 4), array size
    = 8 * 3 = 24. -/
theorem repeat_layout_doc_example_2 :
    repeat_layout ⟨(6 : usize), (4 : usize)⟩ (3 : usize) =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk
          ⟨(24 : usize), (4 : usize)⟩ (8 : usize))) := by
  rfl

/-! ## `layout_errors` boundary anchors

    Transferred from the `tests/alloc.rs::layout_errors` `repeat` assertions
    with `layout = {size:=2, align:=1}`. `align_max = isize::MAX / 2`
    = `(2^63 - 1) / 2` = `2^62 - 1` = `4611686018427387903`. The Ok
    boundary uses `n = align_max`, the Err side `n = align_max + 1`.
    With `align = 1`, stride = `round_up(2, 1) = 2`. -/

/-- Ok side of `layout_errors`: `n = (2^63 - 1) / 2` succeeds (the array
    size is exactly `2 * ((2^63 - 1) / 2) ≤ 2^63 - 1`). -/
theorem repeat_layout_layout_errors_ok :
    ∃ result : rust_primitives.hax.Tuple2 Layout usize,
      repeat_layout ⟨(2 : usize), (1 : usize)⟩
          ((9223372036854775807 : usize) / (2 : usize)) =
        RustM.ok (core_models.result.Result.Ok result) := by
  refine ⟨rust_primitives.hax.Tuple2.mk
            ⟨(9223372036854775806 : usize), (1 : usize)⟩ (2 : usize), ?_⟩
  rfl

/-- Err side of `layout_errors`: `n = (2^63 - 1) / 2 + 1` fails (the array
    size of `2 * n` exceeds `2^63 - 1`). -/
theorem repeat_layout_layout_errors_err :
    repeat_layout ⟨(2 : usize), (1 : usize)⟩
        ((9223372036854775807 : usize) / (2 : usize) + 1) =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  rfl

/-! ## `prop_stride_is_correct_padding` — three stride properties.

    Universal "if Ok" obligations: when `repeat_layout layout n` succeeds with
    payload `Tuple2.mk arr offs`, the stride `offs` satisfies the contract.
    The stride properties (mod, gap) only hold for power-of-two `align`,
    which is a `Layout` invariant; the ALIGNS array in the proptest is
    `[1, 2, 4, 8, 16, 4096, 1 << 30]`, all powers of two. -/

/-- Stride is a multiple of `layout.align`. -/
theorem repeat_layout_ok_stride_mod
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat % layout.align.toNat = 0 := by
  obtain ⟨padded, hpta, _hrp, hoffs⟩ := repeat_layout_ok_inv layout n arr offs h
  obtain ⟨_hnz_redundant, hadd, hpadded⟩ := pad_to_align_ok_inv hpta
  -- offs = padded.size = (size + (align - 1)) &&& ~~~(align - 1)
  have hoffs' :
      offs = (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1) := by
    rw [hoffs, hpadded]
  rw [hoffs']
  -- Show: rounded.toNat % align.toNat = 0
  -- Strategy: rounded &&& (align - 1) = 0 (from bv_padding_key), and
  -- x &&& (align - 1) = x % align (bv_and_mask_eq_mod), so rounded % align = 0.
  -- Need BV-level versions of hnz, hand.
  have hb_nz : layout.align.toBitVec ≠ 0#64 := fun h_eq => hnz (USize64.toBitVec_inj.mp h_eq)
  have hb_and : layout.align.toBitVec &&& (layout.align.toBitVec - 1#64) = 0#64 := by
    have h1 : (layout.align &&& (layout.align - 1)).toBitVec
                = layout.align.toBitVec &&& (layout.align - 1).toBitVec := rfl
    have h2 : (layout.align - 1).toBitVec = layout.align.toBitVec - 1#64 := rfl
    have h0 : (0 : usize).toBitVec = 0#64 := rfl
    have h_ := congrArg USize64.toBitVec hand
    rw [h1, h2, h0] at h_; exact h_
  -- Derive: no overflow in size + (align - 1)
  have hnz_n : layout.align.toNat ≠ 0 :=
    fun h_eq => hnz (USize64.toNat_inj.mp h_eq)
  have h_am1_nat : (layout.align - 1).toNat = layout.align.toNat - 1 := by
    have htn := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ layout.align.toNat by
      rw [usize_one_toNat]; omega)
    rw [usize_one_toNat] at htn; exact htn
  have h_add_lt : layout.size.toNat + (layout.align - 1).toNat < 2 ^ 64 := by
    rw [h_am1_nat]; omega
  have h_no_ovf : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec with
    | false => rfl
    | true => exfalso; rw [USize64.uaddOverflow_iff] at h_eq; omega
  -- Apply bv_padding_key: rounded &&& (a-1) = 0
  obtain ⟨_, h_div_bv, _⟩ :=
    bv_padding_key layout.size.toBitVec layout.align.toBitVec hb_nz hb_and h_no_ovf
  -- Apply bv_and_mask_eq_mod: rounded &&& (a-1) = rounded % a
  have h_mask_eq :=
    bv_and_mask_eq_mod
      (((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toBitVec)
      layout.align.toBitVec hb_nz hb_and
  -- Combine: rounded % a = 0
  have h_div_bv' :
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toBitVec
        &&& (layout.align.toBitVec - 1#64) = 0#64 := h_div_bv
  rw [h_mask_eq] at h_div_bv'
  -- h_div_bv' : rounded.toBitVec % align.toBitVec = 0
  have h_div_nat := congrArg BitVec.toNat h_div_bv'
  rw [BitVec.toNat_umod] at h_div_nat
  exact h_div_nat

/-- Stride is at least the input size. -/
theorem repeat_layout_ok_stride_ge_size
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    layout.size.toNat ≤ offs.toNat := by
  obtain ⟨padded, hpta, _hrp, hoffs⟩ := repeat_layout_ok_inv layout n arr offs h
  obtain ⟨hnz, hadd, hpadded⟩ := pad_to_align_ok_inv hpta
  have hoffs' :
      offs = (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1) := by
    rw [hoffs, hpadded]
  rw [hoffs']
  -- BV-level facts
  have hb_nz : layout.align.toBitVec ≠ 0#64 := fun h_eq => hnz (USize64.toBitVec_inj.mp h_eq)
  -- For `s ≤ rounded`, we need the standard fact `s + (a-1) - (a-1) ≤ rounded`.
  -- Use a separate bv_decide on just `s ≤ ((s + (a-1)) &&& ~~~(a-1))` without `hand`.
  have hnz_n : layout.align.toNat ≠ 0 :=
    fun h_eq => hnz (USize64.toNat_inj.mp h_eq)
  have h_am1_nat : (layout.align - 1).toNat = layout.align.toNat - 1 := by
    have htn := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ layout.align.toNat by
      rw [usize_one_toNat]; omega)
    rw [usize_one_toNat] at htn; exact htn
  have h_add_lt : layout.size.toNat + (layout.align - 1).toNat < 2 ^ 64 := by
    rw [h_am1_nat]; omega
  have h_no_ovf : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec with
    | false => rfl
    | true => exfalso; rw [USize64.uaddOverflow_iff] at h_eq; omega
  -- BV claim: s ≤ ((s + (a - 1)) &&& ~~~(a - 1))  with no-overflow assumption.
  have h_bv_le : layout.size.toBitVec ≤
      ((layout.size.toBitVec + (layout.align.toBitVec - 1#64)) &&& ~~~(layout.align.toBitVec - 1#64))
      := by
    revert h_no_ovf hb_nz; bv_decide
  -- Convert to .toNat
  exact BitVec.le_def.mp h_bv_le

/-- Stride does not over-pad: the gap `offs - size` is strictly less than
    `layout.align`. -/
theorem repeat_layout_ok_stride_gap_lt_align
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat - layout.size.toNat < layout.align.toNat := by
  obtain ⟨padded, hpta, _hrp, hoffs⟩ := repeat_layout_ok_inv layout n arr offs h
  obtain ⟨_hnz_redundant, hadd, hpadded⟩ := pad_to_align_ok_inv hpta
  have hoffs' :
      offs = (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1) := by
    rw [hoffs, hpadded]
  rw [hoffs']
  -- Strategy: use bv_padding_key to get `(rounded - s) < a` at BV level,
  -- then convert via toNat (with no-underflow since rounded ≥ s).
  have hb_nz : layout.align.toBitVec ≠ 0#64 := fun h_eq => hnz (USize64.toBitVec_inj.mp h_eq)
  have hb_and : layout.align.toBitVec &&& (layout.align.toBitVec - 1#64) = 0#64 := by
    have h1 : (layout.align &&& (layout.align - 1)).toBitVec
                = layout.align.toBitVec &&& (layout.align - 1).toBitVec := rfl
    have h2 : (layout.align - 1).toBitVec = layout.align.toBitVec - 1#64 := rfl
    have h0 : (0 : usize).toBitVec = 0#64 := rfl
    have h_ := congrArg USize64.toBitVec hand
    rw [h1, h2, h0] at h_; exact h_
  have hnz_n : layout.align.toNat ≠ 0 :=
    fun h_eq => hnz (USize64.toNat_inj.mp h_eq)
  have h_am1_nat : (layout.align - 1).toNat = layout.align.toNat - 1 := by
    have htn := USize64.toNat_sub_of_le' (show (1 : usize).toNat ≤ layout.align.toNat by
      rw [usize_one_toNat]; omega)
    rw [usize_one_toNat] at htn; exact htn
  have h_add_lt : layout.size.toNat + (layout.align - 1).toNat < 2 ^ 64 := by
    rw [h_am1_nat]; omega
  have h_no_ovf : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow layout.size.toBitVec (layout.align - 1).toBitVec with
    | false => rfl
    | true => exfalso; rw [USize64.uaddOverflow_iff] at h_eq; omega
  obtain ⟨h_le_bv, _, h_lt_bv⟩ :=
    bv_padding_key layout.size.toBitVec layout.align.toBitVec hb_nz hb_and h_no_ovf
  -- h_lt_bv : (rounded - size) < align  at BV level
  -- Show offs.toNat - size.toNat < align.toNat.
  have h_le_nat : layout.size.toNat ≤
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat :=
    BitVec.le_def.mp h_le_bv
  -- (rounded - size).toNat = rounded.toNat - size.toNat (under no underflow)
  have h_sub_nat :
      (((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)) - layout.size).toNat
        = ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
          - layout.size.toNat :=
    USize64.toNat_sub_of_le' h_le_nat
  -- BitVec strict-less gives toNat strict-less.
  have h_lt_nat :
      (((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)) - layout.size).toNat
        < layout.align.toNat :=
    BitVec.lt_def.mp h_lt_bv
  rw [h_sub_nat] at h_lt_nat
  exact h_lt_nat

/-! ## `prop_array_size_is_stride_times_n` — alignment preserved, size = stride * n. -/

/-- The array layout preserves the alignment of the input layout. -/
theorem repeat_layout_ok_align_preserved
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.align = layout.align := by
  obtain ⟨padded, hpta, hrp, _hoffs⟩ := repeat_layout_ok_inv layout n arr offs h
  obtain ⟨_hnz, _hadd, hpadded⟩ := pad_to_align_ok_inv hpta
  have h_arr_eq := repeat_packed_ok_inv hrp
  -- h_arr_eq : arr = Layout.mk (padded.size * n) padded.align
  -- Layout.align of that is padded.align = layout.align (from hpadded).
  rw [h_arr_eq, hpadded]

/-- The array size equals the stride times `n` (no overflow at the `Nat`
    level — the proptest expresses this with `offs.checked_mul(n).expect(_)`). -/
theorem repeat_layout_ok_size_eq_stride_times_n
    (layout : Layout) (n : usize) (arr : Layout) (offs : usize)
    (h : repeat_layout layout n =
      RustM.ok (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.size.toNat = offs.toNat * n.toNat := by
  obtain ⟨padded, hpta, hrp, hoffs⟩ := repeat_layout_ok_inv layout n arr offs h
  have h_arr_eq := repeat_packed_ok_inv hrp
  -- h_arr_eq : arr = Layout.mk (padded.size * n) padded.align
  -- arr.size = padded.size * n
  -- offs = padded.size
  -- Goal: (padded.size * n).toNat = padded.size.toNat * n.toNat
  -- This holds when padded.size * n doesn't overflow.
  -- Need to derive: padded.size.toNat * n.toNat < 2^64.
  -- This follows from: repeat_packed succeeded with Ok.
  -- We can either use repeat_packed_ok_inv arithmetic, or unfold more directly.
  by_cases hn_zero : n = 0
  · subst hn_zero
    rw [h_arr_eq, hoffs]
    simp [USize64.mul_zero, usize_zero_toNat]
  · -- n ≠ 0. From repeat_packed_ok_inv we know arr = padded.size * n.
    -- We also know repeat_packed succeeded, so size * n didn't overflow.
    -- Extract via re-derivation: case-analyze on overflow.
    have h_nomul : ¬ USize64.mulOverflow padded.size n := by
      intro h_ov
      -- If overflow, then `repeat_packed` would have failed via the MAX/n guard.
      have h_ov_nat : 2 ^ 64 ≤ padded.size.toNat * n.toNat := by
        rw [USize64.mulOverflow_iff] at h_ov; exact h_ov
      have hpacked_err := repeat_packed_err_mul_overflow padded n h_ov_nat
      -- hrp : repeat_packed = ok (Ok arr); hpacked_err : repeat_packed = ok (Err _)
      rw [hrp] at hpacked_err
      injection hpacked_err with h_ex
      injection h_ex with h_eq
      cases h_eq
    have h_no_ov_nat : padded.size.toNat * n.toNat < 2 ^ 64 := by
      have h_not_ge : ¬ (padded.size.toNat * n.toNat ≥ 2 ^ 64) := by
        intro h_ge
        have h_iff := (USize64.umulOverflow_iff padded.size n).mpr h_ge
        exact absurd h_iff h_nomul
      omega
    rw [h_arr_eq, hoffs]
    exact USize64.toNat_mul_of_lt h_no_ov_nat

/-! ## `prop_success_iff_fits` — Ok/Err boundary.

    The proptest asserts `got.is_ok() == should_fit`, where `should_fit`
    means `stride.checked_mul(n)` succeeds AND `stride * n ≤ max_size_for_align`.
    Split into the two directions of the iff. The bit-trick `stride` is
    `(size + (align - 1)) &&& ~(align - 1)`. -/

/-- Ok direction of the boundary: when `align` is a power of two with
    `align ≤ 2^63`, `size + align ≤ 2^64` (so the `+ (align - 1)` doesn't
    overflow), and the rounded stride times `n` plus `align` fits within
    `2^63` (i.e. `stride * n ≤ max_size_for_align align`), the function
    returns Ok with the closed form. -/
theorem repeat_layout_ok_when_fits
    (layout : Layout) (n : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64)
    (hmul_bnd :
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        * n.toNat
      + layout.align.toNat ≤ 2 ^ 63) :
    ∃ arr offs,
      repeat_layout layout n =
        RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk arr offs))
      ∧ offs = (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)
      ∧ arr.align = layout.align
      ∧ arr.size.toNat = offs.toNat * n.toNat := by
  -- pad_to_align succeeds and yields { size := rounded, align := layout.align }.
  have hpta := pad_to_align_ok layout hnz hadd
  -- repeat_packed { rounded, align } n succeeds with Ok { rounded * n, align }.
  have hpacked := repeat_packed_ok
                    (Layout.mk
                      (size := (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1))
                      (align := layout.align))
                    n hmul_bnd
  -- Explicit witnesses for ∃ arr offs.
  refine ⟨Layout.mk
            (size := ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)) * n)
            (align := layout.align),
          (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1),
          ?_, rfl, rfl, ?_⟩
  · exact repeat_layout_ok_of_helpers layout n _ _ hpta hpacked
  · -- arr.size.toNat = offs.toNat * n.toNat with arr.size = rounded * n, offs = rounded.
    have hlt :
        ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
          * n.toNat < 2 ^ 64 := by
      have hpow : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
      omega
    exact USize64.toNat_mul_of_lt hlt

/-- Err direction of the boundary: when `align` is a power of two with
    `align ≤ 2^63`, `size + align ≤ 2^64`, but the rounded stride times `n`
    plus `align` exceeds `2^63` while the product still fits in `usize`,
    the function fails. -/
theorem repeat_layout_err_when_too_large
    (layout : Layout) (n : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64)
    (hmul_no_ovf :
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        * n.toNat < 2 ^ 64)
    (htoo_large :
      2 ^ 63 <
        ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
          * n.toNat
        + layout.align.toNat) :
    repeat_layout layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hpta := pad_to_align_ok layout hnz hadd
  -- We need n ≠ 0. If n = 0, rounded * 0 = 0, but htoo_large says
  -- 2^63 < 0 + layout.align.toNat ≤ 2^63. Contradiction (since align ≤ 2^63 from pow2).
  have halign_le : layout.align.toNat ≤ 2 ^ 63 := usize_pow_of_two_le hnz hand
  have hn : n ≠ 0 := by
    intro h_eq
    have hzero : n.toNat = 0 := by rw [h_eq]; rfl
    rw [hzero, Nat.mul_zero, Nat.zero_add] at htoo_large
    omega
  have hpacked := repeat_packed_err_size_too_large
                    (Layout.mk
                      (size := (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1))
                      (align := layout.align))
                    n hn hmul_no_ovf halign_le htoo_large
  exact repeat_layout_err_of_helpers layout n _ hpta hpacked

/-- Err direction (mul-overflow case): when the rounded stride times `n`
    overflows `usize`, the function fails via the `MAX / n` guard. -/
theorem repeat_layout_err_when_mul_overflows
    (layout : Layout) (n : usize)
    (hnz : layout.align ≠ 0)
    (hand : layout.align &&& (layout.align - 1) = 0)
    (hadd : layout.size.toNat + layout.align.toNat ≤ 2 ^ 64)
    (hov : 2 ^ 64 ≤
      ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
        * n.toNat) :
    repeat_layout layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hpta := pad_to_align_ok layout hnz hadd
  have hpacked := repeat_packed_err_mul_overflow
                    (Layout.mk
                      (size := (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1))
                      (align := layout.align))
                    n hov
  exact repeat_layout_err_of_helpers layout n _ hpta hpacked

end Repeat_usizeObligations
