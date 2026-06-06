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

/-- The `Layout` invariant precondition fragment: `align` is a power of two
    (hence `≥ 1`, so the inlined `align - 1` does not underflow). Powers of
    two are exactly the legal alignments enumerated by the Rust property
    tests (`ALIGNS = [1, 2, 4, 8, 16, 4096, 1 << 30]`). Mirrors the `IsPow2`
    helper of the `pad_to_align_usize` reference. -/
def IsPow2 (a : usize) : Prop := ∃ k : Nat, a.toNat = 2 ^ k

/-- Independent oracle for the padded element stride: the least multiple of
    `a` that is `≥ s` (for `a ≥ 1`). This is exactly the Rust test's
    `round_up` reimplementation `if s % a == 0 then s else s + (a - s % a)`,
    and equals the implementation's bitmask `(s + (a-1)) & ~(a-1)` when `a`
    is a power of two. -/
def RoundUp (s a : Nat) : Nat := a * ((s + (a - 1)) / a)

/-! ## Partial-operator definitional unfoldings (transferred from the
    `pad_to_align_usize` / `max_size_for_align_usize` references). -/

/-- Definitional unfolding of the partial `usize` addition. -/
private theorem hax_add_def_usize (x y : usize) :
    x +? y = if USize64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding of the partial `usize` subtraction. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- `x /? y = pure (x / y)` when `y ≠ 0`. -/
private theorem div_pure (x y : usize) (h : y ≠ (0 : usize)) :
    (x /? y : RustM usize) = pure (x / y) := by
  show (rust_primitives.ops.arith.Div.div x y : RustM usize) = pure (x / y)
  show (if y = (0 : usize) then (.fail .divisionByZero : RustM usize)
        else pure (x / y)) = _
  rw [if_neg h]

/-- `x *? y = pure (x * y)` when the product does not overflow. -/
private theorem mul_pure (x y : usize) (h : ¬ USize64.mulOverflow x y) :
    (x *? y : RustM usize) = pure (x * y) := by
  show (rust_primitives.ops.arith.Mul.mul x y : RustM usize) = pure (x * y)
  show (if BitVec.umulOverflow x.toBitVec y.toBitVec then
          (.fail .integerOverflow : RustM usize)
        else pure (x * y)) = _
  have h_bv : BitVec.umulOverflow x.toBitVec y.toBitVec = false := by
    simpa [USize64.mulOverflow] using h
  rw [h_bv]
  rfl

/-- `RustM.ok a >>= f = f a` definitionally. This is the `pure_bind`
    analogue for the `RustM.ok` constructor head: `simp only [pure_bind]`
    matches the `pure` head symbol syntactically and does *not* fire on a
    `RustM.ok`-headed bind (which is what the `pad_to_align_spec` /
    `max_size_for_align_spec` rewrites produce). Holds by `rfl` because
    `RustM.ok a = some (.ok a)` and `ExceptT`'s bind on `some (.ok a)`
    reduces to `f a`. -/
private theorem rustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a >>= f) = f a := rfl

/-! ## `pad_to_align` infrastructure (verbatim from the `pad_to_align_usize`
    reference; the extracted `size_rounded_up_to_custom_align` / `pad_to_align`
    are byte-identical). -/

/-- Bridge: `USize64` bitwise-and projects through to `Nat.land`. -/
private theorem usize_toNat_and (a b : usize) :
    (a &&& b).toNat = a.toNat &&& b.toNat := by
  have h : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_and]

/-- Bridge: `USize64` complement projects through to `2^64 - 1 - n`. -/
private theorem usize_toNat_compl (a : usize) :
    (~~~ a).toNat = 2 ^ 64 - 1 - a.toNat := by
  have h : (~~~ a).toBitVec = ~~~ a.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_not]

/-- Power-of-two bitmask round-down identity at the `Nat` level. -/
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

/-- The exact `Nat` value of the rounded size, under the invariant. -/
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

/-- Under the `Layout` invariant `pad_to_align` succeeds with the masked
    struct. (Same proof as the `pad_to_align_usize` reference.) -/
private theorem pad_to_align_spec (layout : repeat_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    repeat_usize.pad_to_align layout
      = RustM.ok (repeat_usize.Layout.mk
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
  unfold repeat_usize.pad_to_align repeat_usize.size_rounded_up_to_custom_align
  rw [hax_sub_def_usize, if_neg hsub_no]
  simp only [pure_bind]
  rw [hax_add_def_usize, if_neg hadd_no]
  simp only [pure_bind]
  rfl

/-- The padded size's `toNat` equals the `RoundUp` oracle. -/
private theorem padded_size_toNat (layout : repeat_usize.Layout) (k : Nat)
    (hk : layout.align.toNat = 2 ^ k)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ((layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)).toNat
      = RoundUp layout.size.toNat layout.align.toNat := by
  rw [result_toNat layout.size layout.align k hk hnof]
  unfold RoundUp
  rw [hk]

/-! ## `max_size_for_align` infrastructure (verbatim from the
    `max_size_for_align_usize` reference). -/

private theorem const_add :
    (9223372036854775807 : usize) + (1 : usize) = (9223372036854775808 : usize) := by
  decide

private theorem const_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by decide

private theorem no_add_overflow :
    ¬ USize64.addOverflow (9223372036854775807 : usize) (1 : usize) := by decide

/-- For every legal alignment `align ≤ 2^63`, `max_size_for_align` returns
    `(isize::MAX + 1) - align = 2^63 - align`. -/
private theorem max_size_for_align_spec (align : usize)
    (h : align ≤ (9223372036854775808 : usize)) :
    repeat_usize.max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  have hsub : ¬ USize64.subOverflow ((9223372036854775807 : usize) + 1) align := by
    rw [USize64.subOverflow_iff, const_add, const_toNat]
    have hle : align.toNat ≤ 9223372036854775808 := by
      have h' := USize64.le_iff_toNat_le.mp h
      rwa [const_toNat] at h'
    omega
  unfold repeat_usize.max_size_for_align
  rw [hax_add_def_usize, if_neg no_add_overflow]
  simp only [pure_bind]
  rw [hax_sub_def_usize, if_neg hsub, const_add]
  rfl

/-- `(2^63 - align).toNat = 2^63 - align.toNat` when `align ≤ 2^63`. -/
private theorem const_sub_toNat (align : usize)
    (h : align.toNat ≤ 2 ^ 63) :
    ((9223372036854775808 : usize) - align).toNat = 2 ^ 63 - align.toNat := by
  have hval : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have hle : align ≤ (9223372036854775808 : usize) := by
    rw [USize64.le_iff_toNat_le, const_toNat]; omega
  rw [USize64.toNat_sub_of_le _ _ hle, const_toNat]

/-! ## Generic `RustM` bind inversion. -/

/-- The selector-flagged missing infrastructure: inverting a monadic bind.
    If `x >>= f` succeeds with `w`, then `x` succeeded with some `a` and
    `f a` succeeds with `w`. -/
private theorem rustM_bind_eq_ok {α β : Type} {x : RustM α} {f : α → RustM β}
    {w : β} (h : (x >>= f) = RustM.ok w) :
    ∃ a, x = RustM.ok a ∧ f a = RustM.ok w := by
  cases x with
  | none => nomatch h
  | some ex =>
    cases ex with
    | error e => nomatch h
    | ok a => exact ⟨a, rfl, h⟩

/-- `RustM.ok` is injective. -/
private theorem rustM_ok_inj {α : Type} {a b : α}
    (h : (RustM.ok a : RustM α) = RustM.ok b) : a = b := by
  exact Except.ok.inj (Option.some.inj h)

/-! ## `from_size_alignment` characterisation and inversion. -/

/-- Under `align ≤ 2^63`, `from_size_alignment` returns `Err` when the size
    exceeds `2^63 - align` and `Ok (Layout.mk size align)` otherwise. -/
private theorem from_size_alignment_reduce (size align : usize)
    (hal : align.toNat ≤ 2 ^ 63) :
    repeat_usize.from_size_alignment size align =
      (if size.toNat > 2 ^ 63 - align.toNat then
        RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk)
       else
        RustM.ok (core_models.result.Result.Ok
          (repeat_usize.Layout.mk size align))) := by
  have hval : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have hle : align ≤ (9223372036854775808 : usize) := by
    rw [USize64.le_iff_toNat_le, const_toNat]; omega
  unfold repeat_usize.from_size_alignment
  rw [max_size_for_align_spec align hle]
  simp only [rustM_ok_bind]
  have hgt : (size >? ((9223372036854775808 : usize) - align) : RustM Bool)
              = pure (decide (size > (9223372036854775808 : usize) - align)) := rfl
  rw [hgt]
  simp only [pure_bind]
  have hcst : ((9223372036854775808 : usize) - align).toNat = 2 ^ 63 - align.toNat :=
    const_sub_toNat align hal
  by_cases hbig : size.toNat > 2 ^ 63 - align.toNat
  · have hdg : size > (9223372036854775808 : usize) - align := by
      rw [gt_iff_lt, USize64.lt_iff_toNat_lt, hcst]; exact hbig
    rw [if_pos hbig]
    simp only [decide_eq_true hdg]
    rfl
  · have hdg : ¬ size > (9223372036854775808 : usize) - align := by
      rw [gt_iff_lt, USize64.lt_iff_toNat_lt, hcst]; exact Nat.not_lt.mpr (Nat.not_lt.mp hbig)
    rw [if_neg hbig]
    simp only [decide_eq_false hdg]
    rfl

/-- Inversion: if `from_size_alignment size align` succeeds with `Ok r`,
    then `r = Layout.mk size align`.  Holds for any `align`. -/
private theorem from_size_alignment_ok_inv (size align : usize)
    (r : repeat_usize.Layout)
    (h : repeat_usize.from_size_alignment size align
          = RustM.ok (core_models.result.Result.Ok r)) :
    r = repeat_usize.Layout.mk size align := by
  unfold repeat_usize.from_size_alignment at h
  obtain ⟨m, hm, h2⟩ := rustM_bind_eq_ok h
  have hgt : (size >? m : RustM Bool) = pure (decide (size > m)) := rfl
  rw [hgt] at h2
  obtain ⟨b, hb, h3⟩ := rustM_bind_eq_ok h2
  have hbval : b = decide (size > m) := (rustM_ok_inj hb).symm
  subst hbval
  by_cases hsm : size > m
  · simp only [decide_eq_true hsm, if_true] at h3
    have hcontra := rustM_ok_inj h3
    nomatch hcontra
  · simp only [decide_eq_false hsm, if_false] at h3
    have hcontra := rustM_ok_inj h3
    have hr : core_models.result.Result.Ok (repeat_usize.Layout.mk size align)
              = core_models.result.Result.Ok r := hcontra
    injection hr with hrr
    exact hrr.symm

/-! ## `repeat_packed` characterisation. -/

/-- Division/overflow equivalence: `P > usize::MAX / n ↔ P*n overflows`
    (for `n ≠ 0`). -/
private theorem divguard_iff (P n : usize) (hn : n.toNat ≠ 0) :
    (P > (18446744073709551615 : usize) / n) ↔ P.toNat * n.toNat ≥ 2 ^ 64 := by
  have hmaxN : (18446744073709551615 : usize).toNat = 2 ^ 64 - 1 := by decide
  have hdiv : ((18446744073709551615 : usize) / n).toNat
              = (2 ^ 64 - 1) / n.toNat := by
    rw [USize64.toNat_div, hmaxN]
  have hgt : (P > (18446744073709551615 : usize) / n)
              ↔ P.toNat > ((18446744073709551615 : usize) / n).toNat := by
    rw [gt_iff_lt, USize64.lt_iff_toNat_lt]
  rw [hgt, hdiv]
  have hnpos : 0 < n.toNat := Nat.pos_of_ne_zero hn
  constructor
  · intro hP
    have hdm := Nat.div_add_mod (2 ^ 64 - 1) n.toNat
    have hmod : (2 ^ 64 - 1) % n.toNat < n.toNat := Nat.mod_lt _ hnpos
    have hge : (2 ^ 64 - 1) / n.toNat + 1 ≤ P.toNat := by omega
    have hmul1 : ((2 ^ 64 - 1) / n.toNat + 1) * n.toNat ≤ P.toNat * n.toNat :=
      Nat.mul_le_mul_right n.toNat hge
    have hmul2 : ((2 ^ 64 - 1) / n.toNat + 1) * n.toNat
                  = (2 ^ 64 - 1) / n.toNat * n.toNat + n.toNat := by
      rw [Nat.add_mul, Nat.one_mul]
    have hmul3 : (2 ^ 64 - 1) / n.toNat * n.toNat
                  = n.toNat * ((2 ^ 64 - 1) / n.toNat) := Nat.mul_comm _ _
    omega
  · intro hP
    have hdmle : (2 ^ 64 - 1) / n.toNat * n.toNat ≤ 2 ^ 64 - 1 :=
      Nat.div_mul_le_self (2 ^ 64 - 1) n.toNat
    by_contra hcon
    have hcon2 : P.toNat ≤ (2 ^ 64 - 1) / n.toNat := by omega
    have hmul : P.toNat * n.toNat ≤ (2 ^ 64 - 1) / n.toNat * n.toNat :=
      Nat.mul_le_mul_right n.toNat (Nat.le_of_lt_succ (Nat.lt_succ_of_le hcon2))
    omega

/-- `repeat_packed` reduces (for `n ≠ 0`) to: overflow ⇒ `Err`,
    otherwise the inner `from_size_alignment`. -/
private theorem repeat_packed_reduce (L : repeat_usize.Layout) (n : usize)
    (hn : n.toNat ≠ 0) :
    repeat_usize.repeat_packed L n =
      (if L.size.toNat * n.toNat ≥ 2 ^ 64 then
        RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk)
       else
        repeat_usize.from_size_alignment (L.size * n) L.align) := by
  have hn0 : n ≠ (0 : usize) := by
    intro hcon; apply hn; rw [hcon]; rfl
  have hb1 : (n != (0 : usize)) = true := by
    simp [bne, hn0]
  have hne : (n !=? (0 : usize) : RustM Bool) = pure (n != (0 : usize)) := rfl
  have hdiv : ((18446744073709551615 : usize) /? n : RustM usize)
                = pure ((18446744073709551615 : usize) / n) := div_pure _ _ hn0
  have hgt : ∀ q : usize,
      ((repeat_usize.Layout.size L) >? q : RustM Bool)
        = pure (decide ((repeat_usize.Layout.size L) > q)) := fun _ => rfl
  have hand : ∀ a b : Bool, (a &&? b : RustM Bool) = pure (a && b) := fun _ _ => rfl
  unfold repeat_usize.repeat_packed
  simp only [hne, hdiv, hgt, hand, pure_bind, hb1, Bool.true_and]
  by_cases hov : L.size.toNat * n.toNat ≥ 2 ^ 64
  · have hguard : repeat_usize.Layout.size L > (18446744073709551615 : usize) / n :=
      (divguard_iff (repeat_usize.Layout.size L) n hn).mpr hov
    rw [if_pos hov]
    simp only [decide_eq_true hguard, if_true]
    rfl
  · have hovle : ¬ L.size.toNat * n.toNat ≥ 2 ^ 64 := hov
    have hguard : ¬ (repeat_usize.Layout.size L > (18446744073709551615 : usize) / n) := by
      intro hc
      exact hovle ((divguard_iff (repeat_usize.Layout.size L) n hn).mp hc)
    have hnoov : ¬ USize64.mulOverflow (repeat_usize.Layout.size L) n := by
      rw [USize64.mulOverflow_iff]; exact hovle
    rw [if_neg hovle, mul_pure _ _ hnoov]
    simp [decide_eq_false hguard]

/-- `repeat_packed L 0` always fails (division by zero in the inlined
    overflow guard — the non-short-circuit extraction artifact). -/
private theorem repeat_packed_zero_fail (L : repeat_usize.Layout) :
    repeat_usize.repeat_packed L (0 : usize)
      = RustM.fail Error.divisionByZero := by
  have hdiv : ((18446744073709551615 : usize) /? (0 : usize) : RustM usize)
                = RustM.fail Error.divisionByZero := by
    show (rust_primitives.ops.arith.Div.div (18446744073709551615 : usize) (0 : usize)
            : RustM usize) = _
    show (if (0 : usize) = (0 : usize) then (.fail .divisionByZero : RustM usize)
          else pure _) = _
    rw [if_pos rfl]
  have hne0 : ((0 : usize) !=? (0 : usize) : RustM Bool)
                = pure ((0 : usize) != (0 : usize)) := rfl
  unfold repeat_usize.repeat_packed
  simp only [hne0, pure_bind, hdiv]
  rfl

/-! ## `pad_to_align` alignment preservation (inversion). -/

private theorem pad_to_align_align_of_ok (layout padded : repeat_usize.Layout)
    (h : repeat_usize.pad_to_align layout = RustM.ok padded) :
    padded.align = layout.align := by
  unfold repeat_usize.pad_to_align at h
  obtain ⟨ns, hns, h2⟩ := rustM_bind_eq_ok h
  have heq := rustM_ok_inj h2
  rw [← heq]

/-! ## Forward master spec (under the `Layout` invariant, `n ≠ 0`). -/

private theorem repeat_layout_eq
    (layout : repeat_usize.Layout) (n : usize)
    (k : Nat) (hk : layout.align.toNat = 2 ^ k)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0) :
    ∃ P : usize,
      P.toNat = RoundUp layout.size.toNat layout.align.toNat
      ∧ P.toNat % layout.align.toNat = 0
      ∧ layout.size.toNat ≤ P.toNat
      ∧ P.toNat - layout.size.toNat < layout.align.toNat
      ∧ ( ( RoundUp layout.size.toNat layout.align.toNat * n.toNat
              > 2 ^ 63 - layout.align.toNat
            ∧ repeat_usize.repeat_layout layout n
                = RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk) )
        ∨ ( RoundUp layout.size.toNat layout.align.toNat * n.toNat
              ≤ 2 ^ 63 - layout.align.toNat
            ∧ ∃ S : usize,
                S.toNat = RoundUp layout.size.toNat layout.align.toNat * n.toNat
                ∧ repeat_usize.repeat_layout layout n
                    = RustM.ok (core_models.result.Result.Ok
                        (rust_primitives.hax.Tuple2.mk
                          (repeat_usize.Layout.mk S layout.align) P)) ) ) := by
  have hpad := pad_to_align_spec layout ⟨k, hk⟩ hnof
  let P : usize := (layout.size + (layout.align - 1)) &&& ~~~(layout.align - 1)
  have hPnat : P.toNat = RoundUp layout.size.toNat layout.align.toNat :=
    padded_size_toNat layout k hk hnof
  have hklt : k < 64 := by
    have hlt : layout.align.toNat < 2 ^ 64 := layout.align.toNat_lt
    rw [hk] at hlt
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
  have halN : layout.align.toNat ≤ 2 ^ 63 := by
    rw [hk]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hmul0 : P.toNat % layout.align.toNat = 0 := by
    rw [hPnat]; unfold RoundUp; rw [hk]
    exact Nat.mul_mod_right _ _
  have hge : layout.size.toNat ≤ P.toNat := by
    rw [hPnat]; unfold RoundUp; rw [hk]
    have hdm := Nat.div_add_mod (layout.size.toNat + (2 ^ k - 1)) (2 ^ k)
    have hmod : (layout.size.toNat + (2 ^ k - 1)) % 2 ^ k < 2 ^ k :=
      Nat.mod_lt _ (Nat.two_pow_pos k)
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hgap : P.toNat - layout.size.toNat < layout.align.toNat := by
    rw [hPnat]; unfold RoundUp; rw [hk]
    have hdm := Nat.div_add_mod (layout.size.toNat + (2 ^ k - 1)) (2 ^ k)
    have hmod : (layout.size.toNat + (2 ^ k - 1)) % 2 ^ k < 2 ^ k :=
      Nat.mod_lt _ (Nat.two_pow_pos k)
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  refine ⟨P, hPnat, hmul0, hge, hgap, ?_⟩
  have hexp : repeat_usize.repeat_layout layout n
      = (repeat_usize.repeat_packed (repeat_usize.Layout.mk P layout.align) n
          >>= fun res =>
            (match res with
             | core_models.result.Result.Ok r =>
                 repeat_usize.Impl.size (repeat_usize.Layout.mk P layout.align)
                   >>= fun sz =>
                     pure (core_models.result.Result.Ok
                       (rust_primitives.hax.Tuple2.mk r sz))
             | _ => pure (core_models.result.Result.Err
                       repeat_usize.LayoutError.mk))) := by
    unfold repeat_usize.repeat_layout
    rw [hpad]
    rfl
  rw [hexp, repeat_packed_reduce (repeat_usize.Layout.mk P layout.align) n hn]
  by_cases hov : P.toNat * n.toNat ≥ 2 ^ 64
  · rw [if_pos hov]
    left
    refine ⟨?_, ?_⟩
    · rw [← hPnat]
      have hb : (2 : Nat) ^ 63 - layout.align.toNat < 2 ^ 64 := by
        have : (2 : Nat) ^ 63 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
        omega
      omega
    · rfl
  · have hovle : ¬ P.toNat * n.toNat ≥ 2 ^ 64 := hov
    rw [if_neg hovle, from_size_alignment_reduce (P * n) layout.align halN]
    have hmulN : (P * n).toNat = P.toNat * n.toNat :=
      USize64.toNat_mul_of_lt (by omega)
    by_cases hfit : (P * n).toNat > 2 ^ 63 - layout.align.toNat
    · rw [if_pos hfit]
      left
      refine ⟨?_, ?_⟩
      · rw [← hPnat, ← hmulN]; exact hfit
      · rfl
    · have hfit2 : (P * n).toNat ≤ 2 ^ 63 - layout.align.toNat := by omega
      rw [if_neg (Nat.not_lt.mpr hfit2)]
      right
      refine ⟨?_, P * n, ?_, ?_⟩
      · rw [← hPnat, ← hmulN]; exact hfit2
      · rw [hmulN, hPnat]
      · rfl

/-! ## No-`n=0` inversion of `repeat_layout`. -/

/-- `repeat_layout layout 0` never succeeds (the inlined non-short-circuit
    overflow guard divides by `n = 0`). -/
private theorem repeat_layout_zero_not_ok (layout : repeat_usize.Layout)
    (z : core_models.result.Result
          (rust_primitives.hax.Tuple2 repeat_usize.Layout usize)
          repeat_usize.LayoutError) :
    repeat_usize.repeat_layout layout (0 : usize) ≠ RustM.ok z := by
  intro h
  unfold repeat_usize.repeat_layout at h
  obtain ⟨padded, hpad, h2⟩ := rustM_bind_eq_ok h
  obtain ⟨res, hres, h3⟩ := rustM_bind_eq_ok h2
  rw [repeat_packed_zero_fail padded] at hres
  nomatch hres

/-- General inversion: a successful `Ok` result of `repeat_layout` has the
    expected shape. -/
private theorem repeat_layout_ok_inv
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    ∃ padded : repeat_usize.Layout,
      offs = padded.size
      ∧ padded.align = layout.align
      ∧ ¬ USize64.mulOverflow padded.size n
      ∧ arr = repeat_usize.Layout.mk (padded.size * n) layout.align := by
  have hn : n.toNat ≠ 0 := by
    intro h0
    have hz : n = (0 : usize) := by
      have : n.toNat = (0 : usize).toNat := by rw [h0]; rfl
      exact USize64.toNat_inj.mp this
    rw [hz] at h
    exact repeat_layout_zero_not_ok layout _ h
  unfold repeat_usize.repeat_layout at h
  obtain ⟨padded, hpad, h2⟩ := rustM_bind_eq_ok h
  obtain ⟨res, hres, h3⟩ := rustM_bind_eq_ok h2
  have hpalign : padded.align = layout.align := pad_to_align_align_of_ok layout padded hpad
  rw [repeat_packed_reduce padded n hn] at hres
  by_cases hov : padded.size.toNat * n.toNat ≥ 2 ^ 64
  · rw [if_pos hov] at hres
    have hco := rustM_ok_inj hres
    rw [← hco] at h3
    nomatch rustM_ok_inj h3
  · have hovle : ¬ padded.size.toNat * n.toNat ≥ 2 ^ 64 := hov
    rw [if_neg hovle] at hres
    -- `res` is `Ok rr` for some `rr`; extract via `h3`
    cases res with
    | Err e =>
      nomatch rustM_ok_inj h3
    | Ok rr =>
      have hrr : rr = repeat_usize.Layout.mk (padded.size * n) padded.align :=
        from_size_alignment_ok_inv (padded.size * n) padded.align rr hres
      -- now reduce `h3`: matchfn (Ok rr) = Impl.size padded >>= ...
      have h3' : repeat_usize.Impl.size padded
                  >>= (fun sz => pure (core_models.result.Result.Ok
                        (rust_primitives.hax.Tuple2.mk rr sz)))
                  = RustM.ok (core_models.result.Result.Ok
                      (rust_primitives.hax.Tuple2.mk arr offs)) := h3
      obtain ⟨sz, hsz, h4⟩ := rustM_bind_eq_ok h3'
      have hszv : sz = padded.size := by
        have : repeat_usize.Impl.size padded = RustM.ok padded.size := rfl
        rw [this] at hsz
        exact (rustM_ok_inj hsz).symm
      have hfin := rustM_ok_inj h4
      have hfin2 : core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk rr sz)
          = core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs) := hfin
      injection hfin2 with htup
      injection htup with h_arr h_offs
      refine ⟨padded, ?_, hpalign, ?_, ?_⟩
      · rw [← h_offs, hszv]
      · rw [USize64.mulOverflow_iff]; exact hovle
      · rw [← h_arr, hrr, hpalign]

/-! ## Contract obligations. -/

/-- No-panic / totality over the valid input domain (`n ≠ 0`). -/
theorem repeat_layout_total
    (layout : repeat_usize.Layout) (n : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0) :
    ∃ r : core_models.result.Result
            (rust_primitives.hax.Tuple2 repeat_usize.Layout usize)
            repeat_usize.LayoutError,
      repeat_usize.repeat_layout layout n = RustM.ok r := by
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨P, _, _, _, _, hdisj⟩ := repeat_layout_eq layout n k hk hnof hn
  rcases hdisj with ⟨_, herr⟩ | ⟨_, S, _, hok⟩
  · exact ⟨_, herr⟩
  · exact ⟨_, hok⟩

/-- `prop_stride_is_correct_padding`, clause 1: stride is a multiple of
    `align`. -/
theorem repeat_layout_stride_multiple_of_align
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat % layout.align.toNat = 0 := by
  obtain ⟨k, hk⟩ := hpow
  have hn : n.toNat ≠ 0 := by
    intro h0
    have hz : n = (0 : usize) := by
      have : n.toNat = (0 : usize).toNat := by rw [h0]; rfl
      exact USize64.toNat_inj.mp this
    rw [hz] at h
    exact repeat_layout_zero_not_ok layout _ h
  obtain ⟨P, hPnat, hmul0, _, _, hdisj⟩ := repeat_layout_eq layout n k hk hnof hn
  rcases hdisj with ⟨_, herr⟩ | ⟨_, S, _, hok⟩
  · rw [herr] at h
    have hco := rustM_ok_inj h
    nomatch hco
  · rw [hok] at h
    have heq := rustM_ok_inj h
    injection heq with htup
    injection htup with h_arr h_offs
    rw [← h_offs]
    exact hmul0

/-- `prop_stride_is_correct_padding`, clause 2: stride `≥ size`. -/
theorem repeat_layout_stride_not_smaller_than_size
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    layout.size.toNat ≤ offs.toNat := by
  obtain ⟨k, hk⟩ := hpow
  have hn : n.toNat ≠ 0 := by
    intro h0
    have hz : n = (0 : usize) := by
      have : n.toNat = (0 : usize).toNat := by rw [h0]; rfl
      exact USize64.toNat_inj.mp this
    rw [hz] at h
    exact repeat_layout_zero_not_ok layout _ h
  obtain ⟨P, hPnat, _, hge, _, hdisj⟩ := repeat_layout_eq layout n k hk hnof hn
  rcases hdisj with ⟨_, herr⟩ | ⟨_, S, _, hok⟩
  · rw [herr] at h
    have hco := rustM_ok_inj h
    nomatch hco
  · rw [hok] at h
    have heq := rustM_ok_inj h
    injection heq with htup
    injection htup with h_arr h_offs
    rw [← h_offs]
    exact hge

/-- `prop_stride_is_correct_padding`, clause 3: padding gap `< align`. -/
theorem repeat_layout_stride_gap_less_than_align
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    offs.toNat - layout.size.toNat < layout.align.toNat := by
  obtain ⟨k, hk⟩ := hpow
  have hn : n.toNat ≠ 0 := by
    intro h0
    have hz : n = (0 : usize) := by
      have : n.toNat = (0 : usize).toNat := by rw [h0]; rfl
      exact USize64.toNat_inj.mp this
    rw [hz] at h
    exact repeat_layout_zero_not_ok layout _ h
  obtain ⟨P, hPnat, _, _, hgap, hdisj⟩ := repeat_layout_eq layout n k hk hnof hn
  rcases hdisj with ⟨_, herr⟩ | ⟨_, S, _, hok⟩
  · rw [herr] at h
    have hco := rustM_ok_inj h
    nomatch hco
  · rw [hok] at h
    have heq := rustM_ok_inj h
    injection heq with htup
    injection htup with h_arr h_offs
    rw [← h_offs]
    exact hgap

/-- `prop_array_size_is_stride_times_n`, clause 1: alignment preserved. -/
theorem repeat_layout_alignment_preserved
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.align = layout.align := by
  obtain ⟨padded, hoffs, hpalign, hnoov, harr⟩ := repeat_layout_ok_inv layout n arr offs h
  rw [harr]

/-- `prop_array_size_is_stride_times_n`, clause 2: array size = stride·n. -/
theorem repeat_layout_array_size_is_stride_times_n
    (layout : repeat_usize.Layout) (n : usize)
    (arr : repeat_usize.Layout) (offs : usize)
    (h : repeat_usize.repeat_layout layout n
          = RustM.ok (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk arr offs))) :
    arr.size.toNat = offs.toNat * n.toNat := by
  obtain ⟨padded, hoffs, hpalign, hnoov, harr⟩ := repeat_layout_ok_inv layout n arr offs h
  have hmulN : (padded.size * n).toNat = padded.size.toNat * n.toNat := by
    apply USize64.toNat_mul_of_lt
    have hno : ¬ padded.size.toNat * n.toNat ≥ 2 ^ 64 :=
      fun hcon => hnoov ((USize64.mulOverflow_iff (a := padded.size) (b := n)).mpr hcon)
    omega
  rw [harr]
  show (repeat_usize.Layout.mk (padded.size * n) layout.align).size.toNat
        = offs.toNat * n.toNat
  rw [hoffs, hmulN]

/-- `prop_success_iff_fits`, success direction. -/
theorem repeat_layout_ok_when_fits
    (layout : repeat_usize.Layout) (n : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0)
    (hfit : RoundUp layout.size.toNat layout.align.toNat * n.toNat
              ≤ 2 ^ 63 - layout.align.toNat) :
    ∃ (arr : repeat_usize.Layout) (offs : usize),
      repeat_usize.repeat_layout layout n
        = RustM.ok (core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs)) := by
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨P, hPnat, _, _, _, hdisj⟩ := repeat_layout_eq layout n k hk hnof hn
  rcases hdisj with ⟨hbig, _⟩ | ⟨_, S, _, hok⟩
  · exact absurd hfit (Nat.not_le.mpr hbig)
  · exact ⟨_, _, hok⟩

/-- `prop_success_iff_fits`, failure direction. -/
theorem repeat_layout_err_when_not_fits
    (layout : repeat_usize.Layout) (n : usize)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64)
    (hn : n.toNat ≠ 0)
    (hbig : RoundUp layout.size.toNat layout.align.toNat * n.toNat
              > 2 ^ 63 - layout.align.toNat) :
    repeat_usize.repeat_layout layout n
      = RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk) := by
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨P, hPnat, _, _, _, hdisj⟩ := repeat_layout_eq layout n k hk hnof hn
  rcases hdisj with ⟨_, herr⟩ | ⟨hfit, S, _, _⟩
  · exact herr
  · exact absurd hbig (Nat.not_lt.mpr hfit)

/-- Precise model behaviour for `n = 0` — forward-looking scaffolding for
    the obligation below, fully proved. Under the `Layout` invariant
    `pad_to_align` succeeds (`pad_to_align_spec`), and `repeat_packed _ 0`
    fails with `divisionByZero` (`repeat_packed_zero_fail`) because the
    inlined overflow guard `n != 0 && size > usize::MAX / n` was extracted
    by Hax *without* `&&` short-circuiting: the `do`-desugaring hoists the
    bind `(← (usize::MAX /? n))` ahead of the `&&?`, so `usize::MAX /? 0`
    is evaluated unconditionally. Binding a `RustM.fail` short-circuits, so
    the whole call is the fixed value `RustM.fail Error.divisionByZero`. -/
private theorem repeat_layout_zero_fail (layout : repeat_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    repeat_usize.repeat_layout layout (0 : usize)
      = RustM.fail Error.divisionByZero := by
  obtain ⟨k, hk⟩ := hpow
  have hpad := pad_to_align_spec layout ⟨k, hk⟩ hnof
  unfold repeat_usize.repeat_layout
  rw [hpad]
  simp only [rustM_ok_bind]
  rw [repeat_packed_zero_fail]
  rfl

/-- `prop_success_iff_fits`, `n = 0` sub-case (Rust contract:
    `repeat(layout, 0)` is `Ok`).

    **Provably false against the extracted model**, not merely hard. The
    inlined overflow guard `n != 0 && size > usize::MAX / n` was emitted by
    Hax *without* `&&` short-circuiting: the `do`-desugaring hoists the bind
    `(← (usize::MAX /? n))` ahead of the `&&?`, so `usize::MAX /? 0` is
    evaluated unconditionally and `repeat_packed _ 0` reduces to
    `RustM.fail Error.divisionByZero`. This is now established mechanically
    by the fully-proved private helper `repeat_layout_zero_fail`
    (`repeat_layout layout 0 = RustM.fail Error.divisionByZero`), and
    independently by `repeat_layout_zero_not_ok`.

    Stuck sub-goal: after `rw [repeat_layout_zero_fail layout hpow hnof]`
    the goal is
    `∃ arr offs, RustM.fail Error.divisionByZero
                   = RustM.ok (Result.Ok (Tuple2.mk arr offs))`.
    The LHS is a *fixed* value with no dependence on `arr`/`offs`, and
    `RustM.fail`/`RustM.ok` are distinct `Option (Except …)` constructors
    (`some (.error _)` vs `some (.ok _)`), so the equation fails for every
    witness. The existential is therefore unsatisfiable and the statement
    is underivable in a consistent logic — its negation is exactly the
    proved `repeat_layout_zero_not_ok`.

    Structural unblock: the Hax extractor must emit Rust's `&&` with
    short-circuit semantics — i.e. guard the `(← (usize::MAX /? n))` bind
    behind the `n != 0` test in the extracted `repeat_packed` — so that
    `repeat_packed L 0` takes the `Ok` branch. With that single extractor
    change, this obligation closes immediately from a `repeat_layout_eq`
    extended to `n = 0`. No Lean-side lemma can recover it: the defect is
    in the extracted `repeat_packed`, which this stage may not edit. -/
theorem repeat_layout_zero_n_succeeds
    (layout : repeat_usize.Layout)
    (hpow : IsPow2 layout.align)
    (hnof : layout.size.toNat + (layout.align.toNat - 1) < 2 ^ 64) :
    ∃ (arr : repeat_usize.Layout) (offs : usize),
      repeat_usize.repeat_layout layout (0 : usize)
        = RustM.ok (core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs)) := by
  -- Substantive attempt: reduce the LHS to its actual model value via the
  -- proven helper `repeat_layout_zero_fail`. This is real work — it rewrites
  -- the goal using a discharged lemma — and exposes the precise stuck goal.
  rw [repeat_layout_zero_fail layout hpow hnof]
  -- Remaining goal:
  --   ∃ arr offs, RustM.fail Error.divisionByZero
  --                 = RustM.ok (Result.Ok (Tuple2.mk arr offs))
  -- The LHS is now a fixed `RustM.fail`; for every choice of `arr`/`offs`
  -- this is `some (.error _) = some (.ok _)`, false by constructor
  -- disjointness. The existential is unsatisfiable (its negation is the
  -- proved `repeat_layout_zero_not_ok`), so no tactic can close it: the
  -- obligation is provably false against the extracted model. See docstring.
  sorry

/-- `doc_example`, case 1. -/
theorem repeat_layout_example_normal :
    repeat_usize.repeat_layout (repeat_usize.Layout.mk 12 4) 3
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk (repeat_usize.Layout.mk 36 4) 12)) := by
  obtain ⟨P, hPnat, _, _, _, hdisj⟩ :=
    repeat_layout_eq (repeat_usize.Layout.mk 12 4) 3 2 (by decide) (by decide) (by decide)
  have hPv : P.toNat = 12 := by
    rw [hPnat]; decide
  have hP : P = (12 : usize) := by
    apply USize64.toNat_inj.mp; rw [hPv]; rfl
  rcases hdisj with ⟨hbig, _⟩ | ⟨_, S, hS, hok⟩
  · exact absurd hbig (by decide)
  · have hSv : S.toNat = 36 := by rw [hS]; decide
    have hSeq : S = (36 : usize) := by
      apply USize64.toNat_inj.mp; rw [hSv]; rfl
    rw [hok, hP, hSeq]

/-- `doc_example`, case 2. -/
theorem repeat_layout_example_padding_needed :
    repeat_usize.repeat_layout (repeat_usize.Layout.mk 6 4) 3
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk (repeat_usize.Layout.mk 24 4) 8)) := by
  obtain ⟨P, hPnat, _, _, _, hdisj⟩ :=
    repeat_layout_eq (repeat_usize.Layout.mk 6 4) 3 2 (by decide) (by decide) (by decide)
  have hPv : P.toNat = 8 := by
    rw [hPnat]; decide
  have hP : P = (8 : usize) := by
    apply USize64.toNat_inj.mp; rw [hPv]; rfl
  rcases hdisj with ⟨hbig, _⟩ | ⟨_, S, hS, hok⟩
  · exact absurd hbig (by decide)
  · have hSv : S.toNat = 24 := by rw [hS]; decide
    have hSeq : S = (24 : usize) := by
      apply USize64.toNat_inj.mp; rw [hSv]; rfl
    rw [hok, hP, hSeq]

/-- `layout_errors`, success edge. -/
theorem repeat_layout_example_align_max_ok :
    ∃ (arr : repeat_usize.Layout) (offs : usize),
      repeat_usize.repeat_layout (repeat_usize.Layout.mk 2 1)
          4611686018427387903
        = RustM.ok (core_models.result.Result.Ok
            (rust_primitives.hax.Tuple2.mk arr offs)) := by
  obtain ⟨P, hPnat, _, _, _, hdisj⟩ :=
    repeat_layout_eq (repeat_usize.Layout.mk 2 1) 4611686018427387903 0
      (by decide) (by decide) (by decide)
  rcases hdisj with ⟨hbig, _⟩ | ⟨_, S, _, hok⟩
  · exact absurd hbig (by decide)
  · exact ⟨_, _, hok⟩

/-- `layout_errors`, failure edge. -/
theorem repeat_layout_example_align_max_plus_one_err :
    repeat_usize.repeat_layout (repeat_usize.Layout.mk 2 1)
        4611686018427387904
      = RustM.ok (core_models.result.Result.Err repeat_usize.LayoutError.mk) := by
  obtain ⟨P, hPnat, _, _, _, hdisj⟩ :=
    repeat_layout_eq (repeat_usize.Layout.mk 2 1) 4611686018427387904 0
      (by decide) (by decide) (by decide)
  rcases hdisj with ⟨_, herr⟩ | ⟨hfit, S, _, _⟩
  · exact herr
  · exact absurd hfit (by decide)

end Repeat_usizeObligations
