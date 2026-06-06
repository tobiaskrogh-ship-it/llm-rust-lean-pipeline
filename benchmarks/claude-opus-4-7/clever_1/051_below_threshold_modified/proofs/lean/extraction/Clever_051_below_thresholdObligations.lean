-- Companion obligations file for the `clever_051_below_threshold` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_051_below_threshold

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_051_below_thresholdObligations

/-! ## Numeric helpers -/

/-- Helper: `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma
    only matches literal `Pure.pure`; this rewrite handles the `RustM.ok`
    form that simp produces after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `(1 : usize).toNat = 1`. -/
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

/-- `(i + 1).toNat = i.toNat + 1` when no overflow. -/
private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## Step lemmas for `all_below_at`

The three branches of the recursive body, packaged so the strong-induction
work can rewrite the goal directly without re-expanding the `do`-block
at every site. -/

/-- Out-of-bounds step: when `i.toNat ≥ l.val.size`, the function returns `ok true`. -/
private theorem all_below_at_oob (l : RustSlice i64) (t : i64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_051_below_threshold.all_below_at l t i = RustM.ok true := by
  conv => lhs; unfold clever_051_below_threshold.all_below_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Violation step: when `i.toNat < l.val.size` and `t ≤ l[i]`, returns `ok false`. -/
private theorem all_below_at_violation (l : RustSlice i64) (t : i64) (i : usize)
    (hi : i.toNat < l.val.size) (h_ge : t ≤ l.val[i.toNat]'hi) :
    clever_051_below_threshold.all_below_at l t i = RustM.ok false := by
  conv => lhs; unfold clever_051_below_threshold.all_below_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_ge_cond : decide (l.val[i.toNat]'hi ≥ t) = true := by
    rw [decide_eq_true_iff]
    exact h_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_ge_cond]
  rfl

/-- Recursion step: when `i.toNat < l.val.size` and `l[i] < t`,
    the function delegates to `all_below_at l t (i+1)`. -/
private theorem all_below_at_recurse (l : RustSlice i64) (t : i64) (i : usize)
    (hi : i.toNat < l.val.size) (h_lt : l.val[i.toNat]'hi < t) :
    clever_051_below_threshold.all_below_at l t i =
      clever_051_below_threshold.all_below_at l t (i + 1) := by
  conv => lhs; unfold clever_051_below_threshold.all_below_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_ge_cond : decide (l.val[i.toNat]'hi ≥ t) = false := by
    rw [decide_eq_false_iff_not]
    intro h_ge
    have h_le_int : t.toInt ≤ (l.val[i.toNat]'hi).toInt := Int64.le_iff_toInt_le.mp h_ge
    have h_lt_int : (l.val[i.toNat]'hi).toInt < t.toInt := Int64.lt_iff_toInt_lt.mp h_lt
    omega
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_no_overflow : i.toNat + 1 < 2^64 := by omega
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_ge_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv]

/-! ## Workhorse iff: `all_below_at l t i = ok true` ⇔ universal-below-from-i.

Proved by strong induction on the measure `l.val.size - i.toNat`. -/

private theorem all_below_at_iff (l : RustSlice i64) (t : i64) (i : usize) :
    clever_051_below_threshold.all_below_at l t i = RustM.ok true ↔
    ∀ j : Nat, i.toNat ≤ j → ∀ (hj : j < l.val.size), l.val[j]'hj < t := by
  induction hk : (l.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases hbound : l.val.size ≤ i.toNat
    · rw [all_below_at_oob l t i hbound]
      apply iff_of_true rfl
      intro j hij hj
      omega
    · have hbound' : i.toNat < l.val.size := Nat.lt_of_not_le hbound
      by_cases h_below : l.val[i.toNat]'hbound' < t
      · rw [all_below_at_recurse l t i hbound' h_below]
        have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
        have h_no_overflow : i.toNat + 1 < 2^64 := by omega
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
          usize_add_one_toNat i h_no_overflow
        have h_measure_lt : l.val.size - (i + 1).toNat < k := by
          rw [h_i1_toNat]; omega
        have ih_i1 := ih (l.val.size - (i + 1).toNat) h_measure_lt (i + 1) rfl
        rw [ih_i1]
        constructor
        · intro h_all j hij hj
          rcases Nat.lt_or_ge i.toNat j with hlt | hge
          · apply h_all
            rw [h_i1_toNat]; omega
          · have hj_eq : j = i.toNat := by omega
            subst hj_eq
            exact h_below
        · intro h_all j hij hj
          apply h_all j _ hj
          rw [h_i1_toNat] at hij
          omega
      · -- l[i] ≥ t (via the negation of <)
        have h_ge_i : t ≤ l.val[i.toNat]'hbound' := by
          rcases Int.lt_or_le (l.val[i.toNat]'hbound').toInt t.toInt with h | h
          · exfalso; apply h_below; exact Int64.lt_iff_toInt_lt.mpr h
          · exact Int64.le_iff_toInt_le.mpr h
        rw [all_below_at_violation l t i hbound' h_ge_i]
        apply iff_of_false
        · intro hbad
          injection hbad with h1
          injection h1 with h2
          exact Bool.noConfusion h2
        · intro h_all
          have h_lt := h_all i.toNat (Nat.le_refl _) hbound'
          have h_lt_int : (l.val[i.toNat]'hbound').toInt < t.toInt :=
            Int64.lt_iff_toInt_lt.mp h_lt
          have h_le_int : t.toInt ≤ (l.val[i.toNat]'hbound').toInt :=
            Int64.le_iff_toInt_le.mp h_ge_i
          omega

/-! ## False-direction strong-induction lemma. -/

private theorem all_below_at_returns_false_aux (l : RustSlice i64) (t : i64) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      (∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj : j < l.val.size), t ≤ l.val[j]'hj) →
      clever_051_below_threshold.all_below_at l t i = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i hm ⟨j, hij, hj, _⟩
    omega
  | succ m ih =>
    intro i hm ⟨j, hij, hj, hwit⟩
    have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
    have hi_lt : i.toNat < l.val.size := by omega
    by_cases h_now : t ≤ l.val[i.toNat]'hi_lt
    · exact all_below_at_violation l t i hi_lt h_now
    · have h_below : l.val[i.toNat]'hi_lt < t := by
        rcases Int.lt_or_le (l.val[i.toNat]'hi_lt).toInt t.toInt with hh | hh
        · exact Int64.lt_iff_toInt_lt.mpr hh
        · exfalso; apply h_now; exact Int64.le_iff_toInt_le.mpr hh
      have h_j_ne : j ≠ i.toNat := by
        intro heq
        apply h_now
        subst heq
        exact hwit
      have h_j_ge : i.toNat + 1 ≤ j := by omega
      rw [all_below_at_recurse l t i hi_lt h_below]
      have h_no_ov : i.toNat + 1 < 2^64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      apply ih (i + 1) (by rw [h_i1]; omega)
      exact ⟨j, by rw [h_i1]; exact h_j_ge, hj, hwit⟩

/-! ## Top-level obligations -/

/-- Boundary clause (`empty_is_below_any_threshold`):
    on an empty slice, `below_threshold l t = ok true` for every `t`. -/
theorem empty_returns_true (l : RustSlice i64) (t : i64) (hempty : l.val.size = 0) :
    clever_051_below_threshold.below_threshold l t = RustM.ok true := by
  unfold clever_051_below_threshold.below_threshold
  have hi_ge : l.val.size ≤ (0 : usize).toNat := by
    show l.val.size ≤ 0
    omega
  exact all_below_at_oob l t (0 : usize) hi_ge

/-- Soundness direction of `matches_brute_force`:
    if `below_threshold l t` returns `true`, then every element of `l`
    is strictly less than `t`. -/
theorem below_threshold_sound (l : RustSlice i64) (t : i64)
    (h : clever_051_below_threshold.below_threshold l t = RustM.ok true) :
    ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi < t := by
  unfold clever_051_below_threshold.below_threshold at h
  have h_all := (all_below_at_iff l t (0 : usize)).mp h
  intro i hi
  apply h_all i _ hi
  show (0 : USize64).toNat ≤ i
  exact Nat.zero_le _

/-- Completeness direction of `matches_brute_force`:
    if every element of `l` is strictly less than `t`, then
    `below_threshold l t` returns `true`. -/
theorem below_threshold_complete (l : RustSlice i64) (t : i64)
    (h : ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi < t) :
    clever_051_below_threshold.below_threshold l t = RustM.ok true := by
  unfold clever_051_below_threshold.below_threshold
  apply (all_below_at_iff l t (0 : usize)).mpr
  intro j _ hj
  exact h j hj

/-- False-direction of `matches_brute_force` (`some ≥ ⇒ false`):
    if some element of `l` is at least `t`, then `below_threshold l t`
    returns `false`. -/
theorem below_threshold_returns_false (l : RustSlice i64) (t : i64)
    (h : ∃ i : Nat, ∃ (hi : i < l.val.size), t ≤ l.val[i]'hi) :
    clever_051_below_threshold.below_threshold l t = RustM.ok false := by
  unfold clever_051_below_threshold.below_threshold
  obtain ⟨j, hj_size, hj_ge⟩ := h
  apply all_below_at_returns_false_aux l t l.val.size (0 : usize)
  · show l.val.size - (0 : USize64).toNat ≤ l.val.size
    omega
  · refine ⟨j, ?_, hj_size, hj_ge⟩
    show (0 : USize64).toNat ≤ j
    exact Nat.zero_le _

end Clever_051_below_thresholdObligations
