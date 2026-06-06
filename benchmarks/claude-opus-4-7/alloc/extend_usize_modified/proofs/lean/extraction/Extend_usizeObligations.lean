-- Companion obligations file for the `extend_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import extend_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Extend_usizeObligations

open extend_usize

/-! ### Specification helpers (independent of the implementation) -/

/-- `a` is a power of two with `1 ≤ a ≤ 2^63`. -/
private def IsPow2 (a : usize) : Prop :=
  ∃ k : Nat, k ≤ 63 ∧ a.toNat = 2 ^ k

/-- The documented `Layout` precondition shared by both arguments. -/
private def ValidInputs (layout next : extend_usize.Layout) : Prop :=
  IsPow2 (extend_usize.Layout.align layout) ∧
  IsPow2 (extend_usize.Layout.align next) ∧
  (extend_usize.Layout.size layout).toNat ≤ 9223372036854775807 ∧
  (extend_usize.Layout.size next).toNat ≤ 9223372036854775807

/-- Independent oracle for the round-up offset. -/
private def specOffset (layout next : extend_usize.Layout) : Nat :=
  ((extend_usize.Layout.size layout).toNat
      + ((extend_usize.Layout.align next).toNat - 1))
    / (extend_usize.Layout.align next).toNat
    * (extend_usize.Layout.align next).toNat

/-- The combined record fits. -/
private def recordFits (layout next : extend_usize.Layout) : Prop :=
  specOffset layout next + (extend_usize.Layout.size next).toNat
    ≤ 9223372036854775808
        - Nat.max (extend_usize.Layout.align layout).toNat
                  (extend_usize.Layout.align next).toNat

/-! ### Helper lemmas (internal scaffolding) -/

private theorem ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a) >>= f = f a := rfl

private theorem pure_eq_ok {α : Type} (a : α) :
    (pure a : RustM α) = RustM.ok a := rfl

private theorem hgt (a b : usize) :
    (a >? b) = RustM.ok (decide (a > b)) := rfl

private theorem hand (a b : usize) :
    (a &&&? b) = RustM.ok (a &&& b) := rfl

private theorem hcompl (a : usize) :
    (~? a) = RustM.ok (~~~ a) := rfl

private theorem c63_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by simp

private theorem hsub_ok (a b : usize) (hba : b.toNat ≤ a.toNat) :
    (a -? b) = RustM.ok (a - b) := by
  have hno : ¬ BitVec.usubOverflow a.toBitVec b.toBitVec := by
    intro hov
    have hso : USize64.subOverflow a b := hov
    rw [USize64.subOverflow_iff] at hso
    omega
  show (if BitVec.usubOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a - b)) = RustM.ok (a - b)
  rw [if_neg hno]
  rfl

private theorem hadd_ok (a b : usize) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b) = RustM.ok (a + b) := by
  have hno : ¬ BitVec.uaddOverflow a.toBitVec b.toBitVec := by
    rw [USize64.uaddOverflow_iff]; omega
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a + b)) = RustM.ok (a + b)
  rw [if_neg hno]
  rfl

private theorem ok_inj {α : Type} {a b : α} (h : (RustM.ok a) = RustM.ok b) : a = b :=
  Except.ok.inj (Option.some.inj h)

private theorem bind_ok_inv {α β : Type} {x : RustM α} {f : α → RustM β} {r : β}
    (h : (x >>= f) = RustM.ok r) : ∃ v, x = RustM.ok v ∧ f v = RustM.ok r := by
  match x, h with
  | RustM.ok v, h => exact ⟨v, rfl, h⟩
  | RustM.fail e, h =>
      rw [show ((RustM.fail e : RustM α) >>= f) = (RustM.fail e : RustM β) from rfl] at h
      have h1 : some (Except.error e) = some (Except.ok r) := h
      injection h1 with h2
      injection h2
  | RustM.div, h =>
      rw [show ((RustM.div : RustM α) >>= f) = (RustM.div : RustM β) from rfl] at h
      have h1 : (none : Option (Except Error β)) = some (Except.ok r) := h
      injection h1

/-! `max_size_for_align` / `from_size_alignment` ladder (mirrors `align_to`). -/

private theorem msfa_ok (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  apply hsub_ok
  rw [c63_toNat]
  exact hal

private theorem msfa_toNat (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    ((9223372036854775808 : usize) - align).toNat
      = 9223372036854775808 - align.toNat := by
  rw [USize64.toNat_sub_of_le' (by rw [c63_toNat]; exact hal), c63_toNat]

private theorem fsa_core (size align : usize)
    (hal : align.toNat ≤ 9223372036854775808) (b : Bool)
    (hb : decide (size > ((9223372036854775808 : usize) - align)) = b) :
    from_size_alignment size align
      = (if b then RustM.ok (core_models.result.Result.Err LayoutError.mk)
              else RustM.ok (core_models.result.Result.Ok (Layout.mk size align))) := by
  unfold from_size_alignment
  rw [msfa_ok align hal, ok_bind]
  show (size >? ((9223372036854775808 : usize) - align)) >>=
        (fun c => if c then pure (core_models.result.Result.Err LayoutError.mk)
                  else pure (core_models.result.Result.Ok (Layout.mk size align)))
      = (if b then RustM.ok (core_models.result.Result.Err LayoutError.mk)
              else RustM.ok (core_models.result.Result.Ok (Layout.mk size align)))
  rw [hgt, hb, ok_bind]
  show (if b then pure (core_models.result.Result.Err LayoutError.mk)
             else pure (core_models.result.Result.Ok (Layout.mk size align)))
      = (if b then RustM.ok (core_models.result.Result.Err LayoutError.mk)
              else RustM.ok (core_models.result.Result.Ok (Layout.mk size align)))
  cases b <;> rfl

private theorem fsa_ok (size align : usize)
    (hal : align.toNat ≤ 9223372036854775808)
    (hsz : size.toNat ≤ 9223372036854775808 - align.toNat) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Ok (Layout.mk size align)) := by
  have hcond : decide (size > ((9223372036854775808 : usize) - align)) = false := by
    rw [decide_eq_false_iff_not, gt_iff_lt, USize64.lt_iff_toNat_lt,
        msfa_toNat align hal]
    omega
  simpa using fsa_core size align hal false hcond

private theorem fsa_err (size align : usize)
    (hal : align.toNat ≤ 9223372036854775808)
    (hsz : 9223372036854775808 - align.toNat < size.toNat) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hcond : decide (size > ((9223372036854775808 : usize) - align)) = true := by
    rw [decide_eq_true_eq, gt_iff_lt, USize64.lt_iff_toNat_lt,
        msfa_toNat align hal]
    omega
  simpa using fsa_core size align hal true hcond

private theorem fsa_ok_inv {size align : usize} {combined : Layout}
    (h : from_size_alignment size align
          = RustM.ok (core_models.result.Result.Ok combined)) :
    combined = Layout.mk (size := size) (align := align) := by
  unfold from_size_alignment at h
  obtain ⟨M, hM, h⟩ := bind_ok_inv h
  obtain ⟨b, hb, h⟩ := bind_ok_inv h
  by_cases hcond : b = true
  · rw [if_pos hcond, pure_eq_ok] at h
    exact absurd (ok_inj h) (by simp)
  · rw [if_neg hcond, pure_eq_ok] at h
    have hx := ok_inj h
    injection hx with hx'
    exact hx'.symm

/-! ### The key bit-mask round-up lemma -/

private theorem land_high (X k : Nat) (hk : k ≤ 64) (hX : X < 2 ^ 64) :
    X &&& (2 ^ 64 - 2 ^ k) = X / 2 ^ k * 2 ^ k := by
  have hkpos : 0 < (2:Nat) ^ k := Nat.two_pow_pos k
  have h2k_lt : (2:Nat) ^ k - 1 < 2 ^ 64 := by
    have : (2:Nat) ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
    omega
  have hsucc : (2:Nat) ^ k - 1 + 1 = 2 ^ k := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hmask : Nat.testBit (2 ^ 64 - 2 ^ k) i
      = (decide (i < 64) && ! decide (i < k)) := by
    have hrw : (2:Nat) ^ 64 - 2 ^ k = 2 ^ 64 - ((2 ^ k - 1) + 1) := by rw [hsucc]
    rw [hrw, Nat.testBit_two_pow_sub_succ h2k_lt, Nat.testBit_two_pow_sub_one]
  rw [hmask, Nat.testBit_mul_two_pow]
  by_cases hik : i < k
  · have hnk : ¬ k ≤ i := by omega
    simp [hik, hnk]
  · have hki : k ≤ i := by omega
    rw [Nat.testBit_div_two_pow]
    have hsub : i - k + k = i := by omega
    rw [hsub]
    by_cases hi64 : i < 64
    · simp [hik, hi64, hki]
    · have hxi : Nat.testBit X i = false := by
        apply Nat.testBit_lt_two_pow
        have : (2:Nat) ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      simp [hxi, hik, hki]

/-! ### The offset / new-alignment values -/

private def offU (layout next : extend_usize.Layout) : usize :=
  (Layout.size layout + (Layout.align next - 1)) &&& ~~~ (Layout.align next - 1)

private def newAlignOf (layout next : extend_usize.Layout) : usize :=
  if Layout.align layout > Layout.align next
  then Layout.align layout else Layout.align next

private theorem newAlign_toNat (layout next : extend_usize.Layout) :
    (newAlignOf layout next).toNat
      = Nat.max (Layout.align layout).toNat (Layout.align next).toNat := by
  unfold newAlignOf
  by_cases h : Layout.align layout > Layout.align next
  · rw [if_pos h]
    have hle : (Layout.align next).toNat ≤ (Layout.align layout).toNat :=
      Nat.le_of_lt (USize64.lt_iff_toNat_lt.mp h)
    exact (Nat.max_eq_left hle).symm
  · rw [if_neg h]
    have hle : (Layout.align layout).toNat ≤ (Layout.align next).toNat :=
      USize64.le_iff_toNat_le.mp (USize64.not_lt.mp h)
    exact (Nat.max_eq_right hle).symm

private theorem sruca_offU (layout next : extend_usize.Layout)
    (hge1 : 1 ≤ (Layout.align next).toNat)
    (hno : (Layout.size layout).toNat + ((Layout.align next).toNat - 1) < 2 ^ 64) :
    size_rounded_up_to_custom_align (Layout.size layout) (Layout.align next)
      = RustM.ok (offU layout next) := by
  unfold offU
  have h1le : (1 : usize).toNat ≤ (Layout.align next).toNat := by simpa using hge1
  have hm1 : (Layout.align next - 1).toNat = (Layout.align next).toNat - 1 := by
    rw [USize64.toNat_sub_of_le' h1le]; simp
  unfold size_rounded_up_to_custom_align
  rw [hsub_ok (Layout.align next) 1 h1le, ok_bind]
  rw [hadd_ok (Layout.size layout) (Layout.align next - 1) (by rw [hm1]; exact hno), ok_bind]
  rw [hcompl (Layout.align next - 1), ok_bind]
  rw [hand]

private theorem roundup_toNat (layout next : extend_usize.Layout)
    (hpa : IsPow2 (Layout.align next))
    (hs : (Layout.size layout).toNat ≤ 9223372036854775807) :
    (offU layout next).toNat = specOffset layout next := by
  obtain ⟨k, hk63, hak⟩ := hpa
  unfold offU
  have ha1 : 1 ≤ (Layout.align next).toNat := by rw [hak]; exact Nat.one_le_two_pow
  have h1le : (1 : usize).toNat ≤ (Layout.align next).toNat := by simpa using ha1
  have hm1 : (Layout.align next - 1).toNat = (Layout.align next).toNat - 1 := by
    rw [USize64.toNat_sub_of_le' h1le]; simp
  have hk1 : 1 ≤ (2:Nat) ^ k := Nat.one_le_two_pow
  have h2k_le : (2:Nat) ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hk63
  have h263 : (2:Nat) ^ 63 = 9223372036854775808 := by decide
  have h264 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  have hno : (Layout.size layout).toNat + (Layout.align next - 1).toNat < 2 ^ 64 := by
    rw [hm1, hak]; omega
  have hand0 : ((Layout.size layout + (Layout.align next - 1))
                  &&& ~~~ (Layout.align next - 1)).toNat
      = ((Layout.size layout + (Layout.align next - 1)).toNat)
          &&& (2 ^ 64 - 1 - (Layout.align next - 1).toNat) := by
    show (((Layout.size layout + (Layout.align next - 1))
            &&& ~~~ (Layout.align next - 1)).toBitVec.toNat) = _
    have e1 : ((Layout.size layout + (Layout.align next - 1))
                &&& ~~~ (Layout.align next - 1)).toBitVec
        = (Layout.size layout + (Layout.align next - 1)).toBitVec
            &&& ~~~ ((Layout.align next - 1).toBitVec) := rfl
    rw [e1, BitVec.toNat_and, BitVec.toNat_not]
    rfl
  rw [hand0, USize64.toNat_add_of_lt hno, hm1]
  have hmaskval : 2 ^ 64 - 1 - ((Layout.align next).toNat - 1)
      = 2 ^ 64 - (Layout.align next).toNat := by
    rw [hak]; omega
  have hXlt : (Layout.size layout).toNat + (2 ^ k - 1) < 2 ^ 64 := by omega
  rw [hmaskval, hak]
  have hspec : specOffset layout next
      = ((Layout.size layout).toNat + ((Layout.align next).toNat - 1))
          / (Layout.align next).toNat * (Layout.align next).toNat := rfl
  rw [hspec, hak]
  exact land_high ((Layout.size layout).toNat + (2 ^ k - 1)) k (by omega) hXlt

private theorem specOffset_le (s a k : Nat)
    (hs : s ≤ 9223372036854775807) (hk : k ≤ 63) (ha : a = 2 ^ k) :
    (s + (a - 1)) / a * a ≤ 9223372036854775808 := by
  subst ha
  have hapos : 0 < (2:Nat) ^ k := Nat.two_pow_pos k
  have hpow : 2 ^ (63 - k) * 2 ^ k = 9223372036854775808 := by
    rw [← Nat.pow_add]
    have hkk : (63 - k) + k = 63 := by omega
    rw [hkk]
  have hk1 : 1 ≤ (2:Nat) ^ k := Nat.one_le_two_pow
  have hXlt : s + (2 ^ k - 1) < (2 ^ (63 - k) + 1) * 2 ^ k := by
    rw [Nat.add_mul, Nat.one_mul, hpow]
    omega
  have hq : (s + (2 ^ k - 1)) / 2 ^ k < 2 ^ (63 - k) + 1 := by
    rw [Nat.div_lt_iff_lt_mul hapos]; exact hXlt
  have hqle : (s + (2 ^ k - 1)) / 2 ^ k ≤ 2 ^ (63 - k) := Nat.lt_succ_iff.mp hq
  calc (s + (2 ^ k - 1)) / 2 ^ k * 2 ^ k
        ≤ 2 ^ (63 - k) * 2 ^ k := Nat.mul_le_mul_right _ hqle
    _ = 9223372036854775808 := hpow

/-! ### Full reduction of `extend` -/

private theorem extend_unfold (layout next : extend_usize.Layout) :
    extend_usize.extend layout next
      = (size_rounded_up_to_custom_align (Layout.size layout) (Layout.align next))
          >>= fun off => ((off +? (Layout.size next))
          >>= fun nsz => ((from_size_alignment nsz (newAlignOf layout next))
          >>= fun res => match res with
              | core_models.result.Result.Ok l =>
                  RustM.ok (core_models.result.Result.Ok
                    (rust_primitives.hax.Tuple2.mk l off))
              | _ => RustM.ok (core_models.result.Result.Err LayoutError.mk))) := by
  unfold extend_usize.extend newAlignOf
  by_cases hc : Layout.align layout > Layout.align next
  · simp [hgt, ok_bind, pure_bind, hc]
    try rfl
  · simp [hgt, ok_bind, pure_bind, hc]
    try rfl

private theorem extend_ok_eq (layout next : extend_usize.Layout)
    (hpre : ValidInputs layout next) (hf : recordFits layout next) :
    extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk
            (extend_usize.Layout.mk
              (size := offU layout next + Layout.size next)
              (align := newAlignOf layout next))
            (offU layout next))) := by
  obtain ⟨hpl, hpn, hsz, hns⟩ := hpre
  obtain ⟨k, hk63, hak⟩ := hpn
  have h263 : (2:Nat) ^ 63 = 9223372036854775808 := by decide
  have h264 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  have ha1 : 1 ≤ (Layout.align next).toNat := by rw [hak]; exact Nat.one_le_two_pow
  have h2k_le : (2:Nat) ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hk63
  have hna63 : (Layout.align next).toNat ≤ 9223372036854775808 := by
    rw [hak]; omega
  have hsruca_no :
      (Layout.size layout).toNat + ((Layout.align next).toNat - 1) < 2 ^ 64 := by
    rw [hak]; omega
  have hoff : (offU layout next).toNat = specOffset layout next :=
    roundup_toNat layout next ⟨k, hk63, hak⟩ hsz
  have hspec_le : specOffset layout next ≤ 9223372036854775808 := by
    have := specOffset_le (Layout.size layout).toNat (Layout.align next).toNat k hsz hk63 hak
    simpa [specOffset] using this
  have hadd_no :
      (offU layout next).toNat + (Layout.size next).toNat < 2 ^ 64 := by
    rw [hoff]; omega
  have hla63 : (Layout.align layout).toNat ≤ 9223372036854775808 := by
    obtain ⟨kl, hkl, hakl⟩ := hpl
    rw [hakl]
    have : (2:Nat) ^ kl ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hkl
    omega
  have hnewA63 : (newAlignOf layout next).toNat ≤ 9223372036854775808 := by
    rw [newAlign_toNat]; exact Nat.max_le.mpr ⟨hla63, hna63⟩
  have hsz_le : (offU layout next + Layout.size next).toNat
      ≤ 9223372036854775808 - (newAlignOf layout next).toNat := by
    rw [USize64.toNat_add_of_lt hadd_no, hoff, newAlign_toNat]
    exact hf
  rw [extend_unfold,
      sruca_offU layout next ha1 hsruca_no, ok_bind,
      hadd_ok (offU layout next) (Layout.size next) hadd_no, ok_bind,
      fsa_ok (offU layout next + Layout.size next) (newAlignOf layout next)
        hnewA63 hsz_le]
  simp [ok_bind]

private theorem extend_err_eq (layout next : extend_usize.Layout)
    (hpre : ValidInputs layout next) (hnf : ¬ recordFits layout next) :
    extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Err extend_usize.LayoutError.mk) := by
  obtain ⟨hpl, hpn, hsz, hns⟩ := hpre
  obtain ⟨k, hk63, hak⟩ := hpn
  have h263 : (2:Nat) ^ 63 = 9223372036854775808 := by decide
  have h264 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  have ha1 : 1 ≤ (Layout.align next).toNat := by rw [hak]; exact Nat.one_le_two_pow
  have h2k_le : (2:Nat) ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hk63
  have hna63 : (Layout.align next).toNat ≤ 9223372036854775808 := by
    rw [hak]; omega
  have hsruca_no :
      (Layout.size layout).toNat + ((Layout.align next).toNat - 1) < 2 ^ 64 := by
    rw [hak]; omega
  have hoff : (offU layout next).toNat = specOffset layout next :=
    roundup_toNat layout next ⟨k, hk63, hak⟩ hsz
  have hspec_le : specOffset layout next ≤ 9223372036854775808 := by
    have := specOffset_le (Layout.size layout).toNat (Layout.align next).toNat k hsz hk63 hak
    simpa [specOffset] using this
  have hadd_no :
      (offU layout next).toNat + (Layout.size next).toNat < 2 ^ 64 := by
    rw [hoff]; omega
  have hla63 : (Layout.align layout).toNat ≤ 9223372036854775808 := by
    obtain ⟨kl, hkl, hakl⟩ := hpl
    rw [hakl]
    have : (2:Nat) ^ kl ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hkl
    omega
  have hnewA63 : (newAlignOf layout next).toNat ≤ 9223372036854775808 := by
    rw [newAlign_toNat]; exact Nat.max_le.mpr ⟨hla63, hna63⟩
  have hnf' : ¬ (specOffset layout next + (Layout.size next).toNat
      ≤ 9223372036854775808
          - Nat.max (Layout.align layout).toNat (Layout.align next).toNat) := hnf
  have hcond : 9223372036854775808 - (newAlignOf layout next).toNat
      < (offU layout next + Layout.size next).toNat := by
    rw [USize64.toNat_add_of_lt hadd_no, hoff, newAlign_toNat]
    omega
  rw [extend_unfold,
      sruca_offU layout next ha1 hsruca_no, ok_bind,
      hadd_ok (offU layout next) (Layout.size next) hadd_no, ok_bind,
      fsa_err (offU layout next + Layout.size next) (newAlignOf layout next)
        hnewA63 hcond]
  simp [ok_bind]

private theorem extend_ok_shape (layout next : extend_usize.Layout)
    (p : rust_primitives.hax.Tuple2 extend_usize.Layout usize)
    (h : extend_usize.extend layout next
          = RustM.ok (core_models.result.Result.Ok p)) :
    (rust_primitives.hax.Tuple2._0 p).align = newAlignOf layout next := by
  rw [extend_unfold] at h
  obtain ⟨off, hsr, h⟩ := bind_ok_inv h
  obtain ⟨nsz, hadd, h⟩ := bind_ok_inv h
  obtain ⟨res, hfsa, h⟩ := bind_ok_inv h
  cases res with
  | Err e => exact absurd (ok_inj h) (by simp)
  | Ok l =>
      have hpe := ok_inj h
      injection hpe with hpe'
      have hl := fsa_ok_inv hfsa
      subst hpe'
      simp [hl]

private theorem extend_ok_extract (layout next combined : extend_usize.Layout)
    (offset : usize)
    (hpre : ValidInputs layout next)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    recordFits layout next ∧ offset = offU layout next ∧
      combined = extend_usize.Layout.mk
        (size := offU layout next + Layout.size next)
        (align := newAlignOf layout next) := by
  by_cases hf : recordFits layout next
  · rw [extend_ok_eq layout next hpre hf] at hok
    have h2 := ok_inj hok
    injection h2 with h2
    injection h2 with hcomb hoff
    exact ⟨hf, hoff.symm, hcomb.symm⟩
  · exfalso
    rw [extend_err_eq layout next hpre hf] at hok
    exact absurd (ok_inj hok) (by simp)

/-! ### Public obligations -/

theorem extend_err_when_record_does_not_fit
    (layout next : extend_usize.Layout)
    (hpre : ValidInputs layout next)
    (hnf : ¬ recordFits layout next) :
    extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Err extend_usize.LayoutError.mk) :=
  extend_err_eq layout next hpre hnf

theorem extend_ok_when_record_fits
    (layout next : extend_usize.Layout)
    (hpre : ValidInputs layout next)
    (hf : recordFits layout next) :
    ∃ p : rust_primitives.hax.Tuple2 extend_usize.Layout usize,
      extend_usize.extend layout next
        = RustM.ok (core_models.result.Result.Ok p) :=
  ⟨_, extend_ok_eq layout next hpre hf⟩

theorem extend_ok_offset_aligned
    (layout next combined : extend_usize.Layout) (offset : usize)
    (hpre : ValidInputs layout next)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    offset.toNat % (extend_usize.Layout.align next).toNat = 0 := by
  obtain ⟨hf, hoff, hcomb⟩ := extend_ok_extract layout next combined offset hpre hok
  subst hoff
  rw [roundup_toNat layout next hpre.2.1 hpre.2.2.1]
  unfold specOffset
  exact Nat.mul_mod_left _ _

theorem extend_ok_offset_ge_size
    (layout next combined : extend_usize.Layout) (offset : usize)
    (hpre : ValidInputs layout next)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    (extend_usize.Layout.size layout).toNat ≤ offset.toNat := by
  obtain ⟨hf, hoff, hcomb⟩ := extend_ok_extract layout next combined offset hpre hok
  subst hoff
  rw [roundup_toNat layout next hpre.2.1 hpre.2.2.1]
  obtain ⟨k, hk63, hak⟩ := hpre.2.1
  unfold specOffset
  have hapos : 0 < (Layout.align next).toNat := by rw [hak]; exact Nat.two_pow_pos k
  have hdm := Nat.div_add_mod'
    ((Layout.size layout).toNat + ((Layout.align next).toNat - 1)) (Layout.align next).toNat
  have hmod := Nat.mod_lt
    ((Layout.size layout).toNat + ((Layout.align next).toNat - 1)) hapos
  omega

theorem extend_ok_offset_minimal
    (layout next combined : extend_usize.Layout) (offset : usize)
    (hpre : ValidInputs layout next)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    offset.toNat
      < (extend_usize.Layout.size layout).toNat
          + (extend_usize.Layout.align next).toNat := by
  obtain ⟨hf, hoff, hcomb⟩ := extend_ok_extract layout next combined offset hpre hok
  subst hoff
  rw [roundup_toNat layout next hpre.2.1 hpre.2.2.1]
  obtain ⟨k, hk63, hak⟩ := hpre.2.1
  unfold specOffset
  have hapos : 0 < (Layout.align next).toNat := by rw [hak]; exact Nat.two_pow_pos k
  have hle := Nat.div_mul_le_self
    ((Layout.size layout).toNat + ((Layout.align next).toNat - 1)) (Layout.align next).toNat
  omega

theorem extend_ok_combined_align
    (layout next combined : extend_usize.Layout) (offset : usize)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    (extend_usize.Layout.align combined).toNat
      = Nat.max (extend_usize.Layout.align layout).toNat
                (extend_usize.Layout.align next).toNat := by
  have h : extend_usize.Layout.align combined = newAlignOf layout next :=
    extend_ok_shape layout next _ hok
  rw [h, newAlign_toNat]

theorem extend_ok_combined_size
    (layout next combined : extend_usize.Layout) (offset : usize)
    (hpre : ValidInputs layout next)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    (extend_usize.Layout.size combined).toNat
      = offset.toNat + (extend_usize.Layout.size next).toNat := by
  obtain ⟨hf, hoff, hcomb⟩ := extend_ok_extract layout next combined offset hpre hok
  obtain ⟨k, hk63, hak⟩ := hpre.2.1
  have h264 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  have hoffspec := roundup_toNat layout next ⟨k, hk63, hak⟩ hpre.2.2.1
  have hspec_le : specOffset layout next ≤ 9223372036854775808 := by
    have := specOffset_le (Layout.size layout).toNat (Layout.align next).toNat
      k hpre.2.2.1 hk63 hak
    simpa [specOffset] using this
  have hns := hpre.2.2.2
  have hadd_no :
      (offU layout next).toNat + (Layout.size next).toNat < 2 ^ 64 := by
    rw [hoffspec]; omega
  subst hoff
  subst hcomb
  show (offU layout next + Layout.size next).toNat
      = (offU layout next).toNat + (Layout.size next).toNat
  exact USize64.toNat_add_of_lt hadd_no

theorem extend_ok_combined_valid
    (layout next combined : extend_usize.Layout) (offset : usize)
    (hpre : ValidInputs layout next)
    (hok : extend_usize.extend layout next
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk combined offset))) :
    (extend_usize.Layout.size combined).toNat
      ≤ 9223372036854775808 - (extend_usize.Layout.align combined).toNat := by
  obtain ⟨hf, hoff, hcomb⟩ := extend_ok_extract layout next combined offset hpre hok
  obtain ⟨k, hk63, hak⟩ := hpre.2.1
  have h264 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  have hoffspec := roundup_toNat layout next ⟨k, hk63, hak⟩ hpre.2.2.1
  have hspec_le : specOffset layout next ≤ 9223372036854775808 := by
    have := specOffset_le (Layout.size layout).toNat (Layout.align next).toNat
      k hpre.2.2.1 hk63 hak
    simpa [specOffset] using this
  have hns := hpre.2.2.2
  have hadd_no :
      (offU layout next).toNat + (Layout.size next).toNat < 2 ^ 64 := by
    rw [hoffspec]; omega
  subst hcomb
  show (offU layout next + Layout.size next).toNat
      ≤ 9223372036854775808 - (newAlignOf layout next).toNat
  rw [USize64.toNat_add_of_lt hadd_no, hoffspec, newAlign_toNat]
  exact hf

theorem extend_no_panic
    (layout next : extend_usize.Layout)
    (hpre : ValidInputs layout next) :
    ∃ r : core_models.result.Result
            (rust_primitives.hax.Tuple2 extend_usize.Layout usize)
            extend_usize.LayoutError,
      extend_usize.extend layout next = RustM.ok r := by
  by_cases hf : recordFits layout next
  · exact ⟨_, extend_ok_eq layout next hpre hf⟩
  · exact ⟨_, extend_err_eq layout next hpre hf⟩

theorem extend_layout_errors_concrete :
    extend_usize.extend
        (extend_usize.Layout.mk (size := (2 : usize)) (align := (1 : usize)))
        (extend_usize.Layout.mk (size := (9223372036854775807 : usize))
          (align := (1 : usize)))
      = RustM.ok (core_models.result.Result.Err extend_usize.LayoutError.mk) := by
  apply extend_err_eq
  · refine ⟨⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ?_, ?_⟩ <;> decide
  · unfold recordFits specOffset; decide

theorem extend_padding_concrete_1 :
    extend_usize.extend
        (extend_usize.Layout.mk (size := (8 : usize)) (align := (8 : usize)))
        (extend_usize.Layout.mk (size := (4 : usize)) (align := (4 : usize)))
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk
            (extend_usize.Layout.mk (size := (12 : usize)) (align := (8 : usize)))
            (8 : usize))) := by
  rw [extend_ok_eq
        (extend_usize.Layout.mk (size := (8 : usize)) (align := (8 : usize)))
        (extend_usize.Layout.mk (size := (4 : usize)) (align := (4 : usize)))
        (by refine ⟨⟨3, ?_, ?_⟩, ⟨2, ?_, ?_⟩, ?_, ?_⟩ <;> decide)
        (by unfold recordFits specOffset; decide)]
  rfl

theorem extend_padding_concrete_2 :
    extend_usize.extend
        (extend_usize.Layout.mk (size := (3 : usize)) (align := (1 : usize)))
        (extend_usize.Layout.mk (size := (2 : usize)) (align := (4 : usize)))
      = RustM.ok (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk
            (extend_usize.Layout.mk (size := (6 : usize)) (align := (4 : usize)))
            (4 : usize))) := by
  rw [extend_ok_eq
        (extend_usize.Layout.mk (size := (3 : usize)) (align := (1 : usize)))
        (extend_usize.Layout.mk (size := (2 : usize)) (align := (4 : usize)))
        (by refine ⟨⟨0, ?_, ?_⟩, ⟨2, ?_, ?_⟩, ?_, ?_⟩ <;> decide)
        (by unfold recordFits specOffset; decide)]
  rfl

end Extend_usizeObligations
