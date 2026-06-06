-- Companion obligations file for the `repeat_packed_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import repeat_packed_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Repeat_packed_usizeObligations

open repeat_packed_usize

/-! ## Helper lemmas for `usize` arithmetic and the Rust monad. -/

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_2_63_toNat : (9223372036854775808 : usize).toNat = 2 ^ 63 := by decide
private theorem usize_MAX_toNat :
    (18446744073709551615 : usize).toNat = 2 ^ 64 - 1 := by decide

/-- `max_size_for_align align = ok (2^63 - align)` whenever `align.toNat ≤ 2^63`. -/
private theorem max_size_for_align_ok {align : usize}
    (h : align.toNat ≤ 2 ^ 63) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  have hno :
      ¬ (BitVec.usubOverflow (9223372036854775808 : usize).toBitVec
            align.toBitVec = true) := by
    show ¬ (USize64.subOverflow (9223372036854775808 : usize) align = true)
    rw [USize64.subOverflow_iff, usize_2_63_toNat]
    omega
  show (if BitVec.usubOverflow (9223372036854775808 : usize).toBitVec
            align.toBitVec = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure ((9223372036854775808 : usize) - align))
      = RustM.ok ((9223372036854775808 : usize) - align)
  rw [if_neg hno]
  rfl

/-- `(2^63 - align).toNat = 2^63 - align.toNat` under `align ≤ 2^63`. -/
private theorem max_size_for_align_toNat {align : usize}
    (h : align.toNat ≤ 2 ^ 63) :
    ((9223372036854775808 : usize) - align).toNat = 2 ^ 63 - align.toNat := by
  have h_le :
      align.toNat ≤ (9223372036854775808 : usize).toNat := by
    rw [usize_2_63_toNat]; exact h
  rw [USize64.toNat_sub_of_le' h_le, usize_2_63_toNat]

/-- `from_size_alignment size align = ok (Ok ⟨size, align⟩)` when
    `size.toNat + align.toNat ≤ 2^63`. -/
private theorem from_size_alignment_ok {size align : usize}
    (h : size.toNat + align.toNat ≤ 2 ^ 63) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := size) (align := align))) := by
  have halign : align.toNat ≤ 2 ^ 63 := by omega
  have hMax := max_size_for_align_ok halign
  have hSubToNat := max_size_for_align_toNat halign
  -- `¬ size > (2^63 - align)`
  have hNotGt : ¬ ((9223372036854775808 : usize) - align) < size := by
    rw [USize64.lt_iff_toNat_lt, hSubToNat]
    omega
  unfold from_size_alignment
  show (do
      let __do_lift ← max_size_for_align align
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = RustM.ok (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align)))
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
    apply decide_eq_false
    intro h_gt
    exact hNotGt h_gt
  rw [this]
  rfl

/-- `from_size_alignment size align = ok Err` when `align.toNat ≤ 2^63`
    and `size.toNat + align.toNat > 2^63`. -/
private theorem from_size_alignment_err {size align : usize}
    (halign : align.toNat ≤ 2 ^ 63)
    (hsz : 2 ^ 63 < size.toNat + align.toNat) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hMax := max_size_for_align_ok halign
  have hSubToNat := max_size_for_align_toNat halign
  have hGt : ((9223372036854775808 : usize) - align) < size := by
    rw [USize64.lt_iff_toNat_lt, hSubToNat]
    omega
  unfold from_size_alignment
  show (do
      let __do_lift ← max_size_for_align align
      let __do_lift ← (size >? __do_lift)
      if __do_lift = true then
        pure (core_models.result.Result.Err LayoutError.mk)
      else
        pure (core_models.result.Result.Ok
                (Layout.mk (size := size) (align := align))))
    = RustM.ok (core_models.result.Result.Err LayoutError.mk)
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

/-! ## Main contract clauses. -/

/-- Success postcondition (packed size + preserved alignment): when
    `layout.size * n + layout.align ≤ 2^63`, `repeat_packed layout n`
    returns `Ok ⟨layout.size * n, layout.align⟩`. -/
theorem repeat_packed_ok (layout : Layout) (n : usize)
    (hbnd : layout.size.toNat * n.toNat + layout.align.toNat ≤ 2 ^ 63) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Ok
        (Layout.mk (size := layout.size * n) (align := layout.align))) := by
  unfold repeat_packed
  by_cases hn : n = 0
  · -- n = 0 branch: returns from_size_alignment 0 align
    subst hn
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
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := layout.size * (0 : usize)) (align := layout.align)))
    show (do
        let __do_lift ← (pure ((0 : usize) == (0 : usize)) : RustM Bool)
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else _) = _
    have h_beq : ((0 : usize) == (0 : usize)) = true := by decide
    rw [h_beq]
    simp only [pure_bind, if_true]
    -- Goal: from_size_alignment 0 (Layout.align layout) = ok (Ok ⟨layout.size * 0, layout.align⟩)
    have h_mul_zero : layout.size * (0 : usize) = (0 : usize) :=
      USize64.mul_zero
    rw [h_mul_zero]
    have hbnd' : (0 : usize).toNat + (Layout.align layout).toNat ≤ 2 ^ 63 := by
      rw [usize_zero_toNat]; omega
    exact from_size_alignment_ok hbnd'
  · -- n ≠ 0 branch
    have h_eq_decide : decide ((n : usize) = (0 : usize)) = false := decide_eq_false hn
    -- size * n ≤ 2^63 (since the sum is ≤ 2^63)
    have hsn_bound : layout.size.toNat * n.toNat ≤ 2 ^ 63 := by omega
    have hsn_lt : layout.size.toNat * n.toNat < 2 ^ 64 := by
      have : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
      omega
    -- No mul overflow
    have h_nomul : ¬ USize64.mulOverflow layout.size n := by
      rw [USize64.mulOverflow_iff]; omega
    have h_nomul_bv :
        BitVec.umulOverflow layout.size.toBitVec n.toBitVec = false := by
      cases h_eq : BitVec.umulOverflow layout.size.toBitVec n.toBitVec with
      | false => rfl
      | true => exact absurd h_eq h_nomul
    -- (size * n).toNat = size.toNat * n.toNat
    have h_mul_toNat : (layout.size * n).toNat
                        = layout.size.toNat * n.toNat :=
      USize64.toNat_mul_of_lt hsn_lt
    -- n.toNat > 0
    have hn_pos : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
      · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
      · exact hpos
    -- MAX / n is well-defined: pure (MAX / n)
    have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                  = pure ((18446744073709551615 : usize) / n) := by
      show (if n = 0 then (.fail .divisionByZero : RustM usize)
            else pure ((18446744073709551615 : usize) / n)) = _
      rw [if_neg hn]
    -- (MAX / n).toNat = (2^64 - 1) / n.toNat
    have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                        = (2 ^ 64 - 1) / n.toNat := by
      rw [USize64.toNat_div, usize_MAX_toNat]
    -- size ≤ MAX/n since size.toNat * n.toNat < 2^64
    have h_not_gt : ¬ ((18446744073709551615 : usize) / n) < layout.size := by
      rw [USize64.lt_iff_toNat_lt, h_div_toNat]
      have h_le : layout.size.toNat * n.toNat ≤ 2 ^ 64 - 1 := by
        have : (2 : Nat) ^ 63 ≤ 2 ^ 64 - 1 := by decide
        omega
      have h := (Nat.le_div_iff_mul_le hn_pos).mpr h_le
      omega
    -- size *? n = pure (size * n)
    have h_mul : (layout.size *? n : RustM usize)
                  = pure (layout.size * n) := by
      show (if BitVec.umulOverflow layout.size.toBitVec n.toBitVec = true then
              (.fail .integerOverflow : RustM usize)
            else pure (layout.size * n)) = _
      rw [if_neg (by rw [h_nomul_bv]; decide)]
    -- from_size_alignment (size*n) align succeeds
    have h_bnd' : (layout.size * n).toNat + layout.align.toNat ≤ 2 ^ 63 := by
      rw [h_mul_toNat]; exact hbnd
    have h_fsa := from_size_alignment_ok h_bnd'
    -- Now compute the whole expression
    show (do
        let __do_lift ← ((n : usize) ==? (0 : usize) : RustM Bool)
        if __do_lift = true then
          from_size_alignment (0 : usize) (Layout.align layout)
        else
          do
            let __do_lift ← ((18446744073709551615 : usize) /? n)
            let __do_lift ← (Layout.size layout >? __do_lift)
            if __do_lift = true then
              pure (core_models.result.Result.Err LayoutError.mk)
            else
              do
                let __do_lift ← (Layout.size layout *? n)
                from_size_alignment __do_lift (Layout.align layout))
      = _
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
    rw [h_div]
    simp only [pure_bind]
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
    have h_dec_false : decide (Layout.size layout > (18446744073709551615 : usize) / n) = false := by
      apply decide_eq_false
      intro h_gt
      exact h_not_gt h_gt
    rw [h_dec_false]
    simp only [Bool.false_eq_true, if_false]
    rw [h_mul]
    simp only [pure_bind]
    exact h_fsa

/-- Failure clause (size exceeds `isize::MAX` after multiplication). -/
theorem repeat_packed_err_size_too_large (layout : Layout) (n : usize)
    (hn : n ≠ 0)
    (hnomul : layout.size.toNat * n.toNat < 2 ^ 64)
    (halign : layout.align.toNat ≤ 2 ^ 63)
    (hsz : 2 ^ 63 < layout.size.toNat * n.toNat + layout.align.toNat) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  unfold repeat_packed
  have h_eq_decide : decide ((n : usize) = (0 : usize)) = false := decide_eq_false hn
  -- No mul overflow
  have h_nomul : ¬ USize64.mulOverflow layout.size n := by
    rw [USize64.mulOverflow_iff]; omega
  have h_nomul_bv :
      BitVec.umulOverflow layout.size.toBitVec n.toBitVec = false := by
    cases h_eq : BitVec.umulOverflow layout.size.toBitVec n.toBitVec with
    | false => rfl
    | true => exact absurd h_eq h_nomul
  -- (size * n).toNat = size.toNat * n.toNat
  have h_mul_toNat : (layout.size * n).toNat
                      = layout.size.toNat * n.toNat :=
    USize64.toNat_mul_of_lt hnomul
  -- n.toNat > 0
  have hn_pos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
    · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
    · exact hpos
  -- MAX /? n = pure (MAX / n)
  have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                = pure ((18446744073709551615 : usize) / n) := by
    show (if n = 0 then (.fail .divisionByZero : RustM usize)
          else pure ((18446744073709551615 : usize) / n)) = _
    rw [if_neg hn]
  -- (MAX / n).toNat = (2^64 - 1) / n.toNat
  have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                      = (2 ^ 64 - 1) / n.toNat := by
    rw [USize64.toNat_div, usize_MAX_toNat]
  -- size ≤ MAX/n since size.toNat * n.toNat < 2^64 ⟹ size.toNat ≤ (2^64-1)/n.toNat
  have h_not_gt : ¬ ((18446744073709551615 : usize) / n) < layout.size := by
    rw [USize64.lt_iff_toNat_lt, h_div_toNat]
    have h_le : layout.size.toNat * n.toNat ≤ 2 ^ 64 - 1 := by omega
    have h := (Nat.le_div_iff_mul_le hn_pos).mpr h_le
    omega
  -- size *? n = pure (size * n)
  have h_mul : (layout.size *? n : RustM usize)
                = pure (layout.size * n) := by
    show (if BitVec.umulOverflow layout.size.toBitVec n.toBitVec = true then
            (.fail .integerOverflow : RustM usize)
          else pure (layout.size * n)) = _
    rw [if_neg (by rw [h_nomul_bv]; decide)]
  -- from_size_alignment (size*n) align returns Err
  have h_sum : 2 ^ 63 < (layout.size * n).toNat + layout.align.toNat := by
    rw [h_mul_toNat]; exact hsz
  have h_fsa := from_size_alignment_err halign h_sum
  -- Now compute the whole expression
  show (do
      let __do_lift ← ((n : usize) ==? (0 : usize) : RustM Bool)
      if __do_lift = true then
        from_size_alignment (0 : usize) (Layout.align layout)
      else
        do
          let __do_lift ← ((18446744073709551615 : usize) /? n)
          let __do_lift ← (Layout.size layout >? __do_lift)
          if __do_lift = true then
            pure (core_models.result.Result.Err LayoutError.mk)
          else
            do
              let __do_lift ← (Layout.size layout *? n)
              from_size_alignment __do_lift (Layout.align layout))
    = _
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
  rw [h_div]
  simp only [pure_bind]
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
  have h_dec_false : decide (Layout.size layout > (18446744073709551615 : usize) / n) = false := by
    apply decide_eq_false
    intro h_gt
    exact h_not_gt h_gt
  rw [h_dec_false]
  simp only [Bool.false_eq_true, if_false]
  rw [h_mul]
  simp only [pure_bind]
  exact h_fsa

/-- Failure clause (multiplication overflow). -/
theorem repeat_packed_err_mul_overflow (layout : Layout) (n : usize)
    (hov : 2 ^ 64 ≤ layout.size.toNat * n.toNat) :
    repeat_packed layout n =
      RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  unfold repeat_packed
  -- n ≠ 0: otherwise size * 0 = 0 < 2^64, contradicting hov
  have hn : n ≠ 0 := by
    intro h_eq
    have h_n_zero : n.toNat = 0 := by rw [h_eq]; rfl
    rw [h_n_zero, Nat.mul_zero] at hov
    exact absurd hov (by decide)
  have h_eq_decide : decide ((n : usize) = (0 : usize)) = false := decide_eq_false hn
  -- n.toNat > 0
  have hn_pos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
    · exfalso; apply hn; apply USize64.toNat_inj.mp; rw [h0]; rfl
    · exact hpos
  -- MAX /? n = pure (MAX / n)
  have h_div : ((18446744073709551615 : usize) /? n : RustM usize)
                = pure ((18446744073709551615 : usize) / n) := by
    show (if n = 0 then (.fail .divisionByZero : RustM usize)
          else pure ((18446744073709551615 : usize) / n)) = _
    rw [if_neg hn]
  -- (MAX / n).toNat = (2^64 - 1) / n.toNat
  have h_div_toNat : ((18446744073709551615 : usize) / n).toNat
                      = (2 ^ 64 - 1) / n.toNat := by
    rw [USize64.toNat_div, usize_MAX_toNat]
  -- size > MAX/n since size.toNat * n.toNat ≥ 2^64
  have h_gt : ((18446744073709551615 : usize) / n) < layout.size := by
    rw [USize64.lt_iff_toNat_lt, h_div_toNat]
    -- need (2^64 - 1)/n.toNat < size.toNat
    -- Use Nat.lt_of_mul_lt_mul_right: q*n ≤ 2^64-1 < size*n ⟹ q < size.
    have h_qn : ((2 ^ 64 - 1) / n.toNat) * n.toNat ≤ 2 ^ 64 - 1 :=
      Nat.div_mul_le_self _ _
    have h_lt :
        ((2 ^ 64 - 1) / n.toNat) * n.toNat < layout.size.toNat * n.toNat := by omega
    exact Nat.lt_of_mul_lt_mul_right h_lt
  -- Now compute the whole expression
  show (do
      let __do_lift ← ((n : usize) ==? (0 : usize) : RustM Bool)
      if __do_lift = true then
        from_size_alignment (0 : usize) (Layout.align layout)
      else
        do
          let __do_lift ← ((18446744073709551615 : usize) /? n)
          let __do_lift ← (Layout.size layout >? __do_lift)
          if __do_lift = true then
            pure (core_models.result.Result.Err LayoutError.mk)
          else
            do
              let __do_lift ← (Layout.size layout *? n)
              from_size_alignment __do_lift (Layout.align layout))
    = _
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
  rw [h_div]
  simp only [pure_bind]
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

end Repeat_packed_usizeObligations
