-- Companion obligations file for the `clever_129_tri` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_129_tri

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_129_triObligations

/-! ## Specification oracle (`tri_nat`) — pure Nat-level semantics of `tri_at`.

For position `i`, the value pushed by the Rust loop is:

* `i = 0` ⇒ 3
* `i = 1` ⇒ 3
* even `i ≥ 2` ⇒ `1 + i / 2`
* odd  `i ≥ 3` ⇒ `1 + (i-1)/2 + tri_nat(i-2) + 1 + (i+1)/2`.

The closed-form for the odd branch (used for bound computation) is
`tri_nat (2k+1) = (k+1)(k+3)` for `k ≥ 0`, which we prove inductively.
-/
private def tri_nat : Nat → Nat
  | 0 => 3
  | 1 => 3
  | i+2 =>
      if (i+2) % 2 = 0 then 1 + (i+2)/2
      else 1 + ((i+2) - 1)/2 + tri_nat i + 1 + ((i+2)+1)/2

private theorem tri_nat_zero : tri_nat 0 = 3 := rfl
private theorem tri_nat_one  : tri_nat 1 = 3 := rfl

/-- Even unfolding. -/
private theorem tri_nat_even (i : Nat) (h_ge : 2 ≤ i) (h_even : i % 2 = 0) :
    tri_nat i = 1 + i / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  show (if (j+2) % 2 = 0 then 1 + (j+2)/2 else _) = 1 + (j+2)/2
  rw [if_pos h_even]

/-- Odd unfolding. -/
private theorem tri_nat_odd (i : Nat) (h_ge : 3 ≤ i) (h_odd : i % 2 = 1) :
    tri_nat i = 1 + (i - 1)/2 + tri_nat (i - 2) + 1 + (i + 1)/2 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  have h_ne : (j + 2) % 2 ≠ 0 := by omega
  show (if (j+2) % 2 = 0 then _ else 1 + ((j+2) - 1)/2 + tri_nat j + 1 + ((j+2)+1)/2)
      = 1 + ((j+2) - 1)/2 + tri_nat ((j+2) - 2) + 1 + ((j+2)+1)/2
  rw [if_neg h_ne]
  show 1 + ((j+2) - 1)/2 + tri_nat j + 1 + ((j+2)+1)/2 =
        1 + ((j+2) - 1)/2 + tri_nat ((j+2) - 2) + 1 + ((j+2)+1)/2
  have h_sub : (j + 2) - 2 = j := by omega
  rw [h_sub]

/-! ## tri_nat closed form for odd indices: `tri_nat (2k+1) = (k+1)(k+3)`. -/

private theorem mul_expand (k : Nat) :
    (k + 1 + 1) * (k + 1 + 3) = (k + 1) * (k + 3) + 2 * k + 5 := by
  -- ((k+1)+1)*((k+3)+1) = (k+1)*(k+3) + (k+1)*1 + 1*((k+3)+1)
  --                     = (k+1)*(k+3) + (k+1) + (k+3+1)
  have h1 : (k + 1 + 1) * (k + 1 + 3)
      = (k + 1) * (k + 1 + 3) + 1 * (k + 1 + 3) := Nat.add_mul _ _ _
  have h2 : (k + 1) * (k + 1 + 3)
      = (k + 1) * (k + 3) + (k + 1) * 1 := by
    show (k + 1) * ((k + 3) + 1) = (k + 1) * (k + 3) + (k + 1) * 1
    exact Nat.mul_add _ _ _
  rw [h1, h2, Nat.mul_one, Nat.one_mul]
  omega

private theorem tri_nat_odd_closed_form : ∀ (k : Nat),
    tri_nat (2*k + 1) = (k + 1) * (k + 3) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_ge : 3 ≤ 2 * (k + 1) + 1 := by omega
    have h_odd : (2 * (k + 1) + 1) % 2 = 1 := by omega
    rw [tri_nat_odd _ h_ge h_odd]
    have h_minus : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
    rw [h_minus, ih]
    have h_m1 : (2 * (k + 1) + 1 - 1) / 2 = k + 1 := by omega
    have h_p1 : (2 * (k + 1) + 1 + 1) / 2 = k + 2 := by omega
    rw [h_m1, h_p1]
    -- goal: 1 + (k + 1) + (k + 1) * (k + 3) + 1 + (k + 2) = (k + 1 + 1) * (k + 1 + 3)
    have h_expand := mul_expand k
    omega

/-! ## tri_nat bound for i ≤ 2^33 - 2. -/

/-- The success bound: at `n ≤ N`, every value pushed fits in `u64`,
    intermediate arithmetic doesn't overflow, and the iteration succeeds. -/
private def N_bound : Nat := 2^33 - 2

private theorem N_bound_eq : N_bound = 8589934590 := by decide

private theorem N_bound_lt_2_64 : N_bound + 1 < 2 ^ 64 := by decide

/-- For odd `i ≤ N_bound`, `tri_nat i ≤ 2^64 - 1`. -/
private theorem tri_nat_odd_lt (i : Nat) (h_le : i ≤ N_bound)
    (h_odd : i % 2 = 1) : tri_nat i ≤ 2 ^ 64 - 1 := by
  -- Write i = 2k + 1.
  obtain ⟨k, rfl⟩ : ∃ k, i = 2 * k + 1 := by
    refine ⟨(i - 1) / 2, ?_⟩; omega
  rw [tri_nat_odd_closed_form]
  -- (k+1)(k+3) ≤ ?
  have h_k : 2 * k + 1 ≤ N_bound := h_le
  have h_k_lt : k + 1 ≤ 2 ^ 32 - 1 := by
    have : k ≤ 2 ^ 32 - 2 := by
      rw [N_bound_eq] at h_k
      omega
    omega
  -- (k+1)(k+3) ≤ (2^32 - 1) * (2^32 + 1) = 2^64 - 1.
  have h_kk : k + 3 ≤ 2 ^ 32 + 1 := by
    have : k ≤ 2 ^ 32 - 2 := by rw [N_bound_eq] at h_k; omega
    omega
  have h_prod : (k + 1) * (k + 3) ≤ (2 ^ 32 - 1) * (2 ^ 32 + 1) :=
    Nat.mul_le_mul h_k_lt h_kk
  have h_final : (2 ^ 32 - 1) * (2 ^ 32 + 1) = 2 ^ 64 - 1 := by decide
  rw [h_final] at h_prod
  exact h_prod

/-- For even `i ≤ N_bound`, `tri_nat i < 2 ^ 64`. -/
private theorem tri_nat_even_lt (i : Nat) (h_le : i ≤ N_bound)
    (h_even : i % 2 = 0) (h_ge : 2 ≤ i) : tri_nat i < 2 ^ 64 := by
  rw [tri_nat_even _ h_ge h_even]
  -- 1 + i/2 ≤ 1 + N/2 = 1 + 2^32 - 1 = 2^32.
  have h_div : i / 2 ≤ N_bound / 2 := Nat.div_le_div_right h_le
  have h_N_div : N_bound / 2 = 2 ^ 32 - 1 := by decide
  rw [h_N_div] at h_div
  have h_pow : (2 ^ 32 : Nat) < 2 ^ 64 := by decide
  omega

/-- Overall: tri_nat i < 2^64 for i ≤ N_bound. -/
private theorem tri_nat_lt_2_64 (i : Nat) (h_le : i ≤ N_bound) :
    tri_nat i < 2 ^ 64 := by
  by_cases h0 : i = 0
  · subst h0; rw [tri_nat_zero]; decide
  by_cases h1 : i = 1
  · subst h1; rw [tri_nat_one]; decide
  have h_ge : 2 ≤ i := by omega
  rcases Nat.mod_two_eq_zero_or_one i with h_par | h_par
  · exact tri_nat_even_lt i h_le h_par h_ge
  · have h_le_sub_one : tri_nat i ≤ 2 ^ 64 - 1 := tri_nat_odd_lt i h_le h_par
    have h_pow : (1 : Nat) ≤ 2 ^ 64 := by decide
    omega

/-! ## Helpers (port from `clever_105_f`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat  : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat  : (2 : u64).toNat = 2 := rfl
private theorem u64_three_toNat : (3 : u64).toNat = 3 := rfl

private theorem usize_size_eq_2_64 : USize64.size = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

/-- `d *? d' = pure (d * d')` when `d.toNat * d'.toNat` fits in `u64`. -/
private theorem mul_pure (d d' : u64) (h : d.toNat * d'.toNat < 2 ^ 64) :
    (d *? d' : RustM u64) = pure (d * d') := by
  show (rust_primitives.ops.arith.Mul.mul d d' : RustM u64) = pure (d * d')
  show (if BitVec.umulOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d * d')) = _
  have h_no : ¬ UInt64.mulOverflow d d' := by
    rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow d.toBitVec d'.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

/-- `d +? d' = pure (d + d')` when `d.toNat + d'.toNat` fits in `u64`. -/
private theorem add_pure (d d' : u64) (h : d.toNat + d'.toNat < 2 ^ 64) :
    (d +? d' : RustM u64) = pure (d + d') := by
  show (rust_primitives.ops.arith.Add.add d d' : RustM u64) = pure (d + d')
  show (if BitVec.uaddOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d + d')) = _
  have h_no : ¬ UInt64.addOverflow d d' := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow d.toBitVec d'.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `d -? d' = pure (d - d')` when `d.toNat ≥ d'.toNat`. -/
private theorem sub_pure (d d' : u64) (h : d'.toNat ≤ d.toNat) :
    (d -? d' : RustM u64) = pure (d - d') := by
  show (rust_primitives.ops.arith.Sub.sub d d' : RustM u64) = pure (d - d')
  show (if BitVec.usubOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d - d')) = _
  have h_no : ¬ UInt64.subOverflow d d' := by
    rw [UInt64.subOverflow_iff]; omega
  have h_bv : BitVec.usubOverflow d.toBitVec d'.toBitVec = false := by
    simpa [UInt64.subOverflow] using h_no
  rw [h_bv]; rfl

/-- `n %? d = pure (n % d)` when `d ≠ 0`. -/
private theorem mod_pure (n d : u64) (h : d ≠ 0) :
    (n %? d : RustM u64) = pure (n % d) := by
  show (rust_primitives.ops.arith.Rem.rem n d : RustM u64) = pure (n % d)
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n % d)) = _
  rw [if_neg h]

/-- `n /? d = pure (n / d)` when `d ≠ 0`. -/
private theorem div_pure (n d : u64) (h : d ≠ 0) :
    (n /? d : RustM u64) = pure (n / d) := by
  show (rust_primitives.ops.arith.Div.div n d : RustM u64) = pure (n / d)
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n / d)) = _
  rw [if_neg h]

/-- `(d + 1).toNat = d.toNat + 1` when the sum fits. -/
private theorem succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

/-- `d +? d' = .fail .integerOverflow` when the sum overflows. -/
private theorem add_fail (d d' : u64) (h : 2 ^ 64 ≤ d.toNat + d'.toNat) :
    (d +? d' : RustM u64) = .fail .integerOverflow := by
  show (rust_primitives.ops.arith.Add.add d d' : RustM u64) = .fail .integerOverflow
  show (if BitVec.uaddOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d + d')) = _
  have h_ov : UInt64.addOverflow d d' := by
    rw [UInt64.addOverflow_iff]; exact h
  have h_bv : BitVec.uaddOverflow d.toBitVec d'.toBitVec = true := by
    simpa [UInt64.addOverflow] using h_ov
  rw [h_bv]; rfl

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_one_size (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

/-- Indexing the last element of `push_one acc x` gives `x`. Uses that
    `as ++ #[x]` is definitionally `as.push x`, so the canonical
    `Array.getElem_push_eq` closes the goal directly. -/
private theorem push_one_back (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size)
    (hb : acc.val.size < (push_one acc x h).val.size) :
    ((push_one acc x h).val[acc.val.size]'hb) = x :=
  Array.getElem_push_eq

/-- The earlier elements of `push_one acc x` come from `acc`. -/
private theorem push_one_left (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size)
    (j : Nat) (hj_lt : j < acc.val.size)
    (hb : j < (push_one acc x h).val.size) :
    ((push_one acc x h).val[j]'hb) = (acc.val[j]'hj_lt) := by
  show ((acc.val ++ #[x])[j]'hb) = acc.val[j]'hj_lt
  exact Array.getElem_append_left hj_lt

/-! ## Branch lemma: OOB.

When `i > n`, the recursion terminates immediately with `acc`. -/
private theorem tri_at_oob (n i : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h : n.toNat < i.toNat) :
    clever_129_tri.tri_at n i acc = RustM.ok acc := by
  conv => lhs; unfold clever_129_tri.tri_at
  have h_gt : i > n := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (i > n) = true := decide_eq_true h_gt
  simp only [show (i >? n : RustM Bool) = pure (decide (i > n)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ## Step lemma: `i = 0`. -/
private theorem tri_at_step_zero (n : u64)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_129_tri.tri_at n 0 acc =
      clever_129_tri.tri_at n 1 (push_one acc 3 h_acc) := by
  conv => lhs; unfold clever_129_tri.tri_at
  -- `(0 : u64) > n` is false (since 0 ≤ n.toNat trivially).
  have h_not_gt : ¬ (0 : u64) > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    rw [u64_zero_toNat] at this; omega
  have h_dec_gt : decide ((0 : u64) > n) = false := decide_eq_false h_not_gt
  -- (0 ==? 0) is `pure true`.
  have h_eq0 : ((0 : u64) ==? (0 : u64) : RustM Bool) = pure true := by
    show pure ((0 : u64) == (0 : u64)) = pure true
    rfl
  -- (0 + 1) reduces by add_pure.
  have h_add_one : ((0 : u64) +? (1 : u64) : RustM u64) = RustM.ok ((0 : u64) + 1) :=
    add_pure 0 1 (by rw [u64_zero_toNat, u64_one_toNat]; decide)
  -- (0 : u64) + 1 = 1 in u64.
  have h_zero_plus_one : ((0 : u64) + 1 : u64) = (1 : u64) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add_of_lt (by rw [u64_zero_toNat, u64_one_toNat]; decide)]
    rw [u64_zero_toNat, u64_one_toNat]
  simp only [show ((0 : u64) >? n : RustM Bool) = pure (decide ((0 : u64) > n)) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_eq0]
  -- Reduce unsize + extend_from_slice.
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[(3 : u64)] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(3 : u64)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[(3 : u64)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[(3 : u64)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc 3 h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind, h_add_one, h_zero_plus_one]

/-! ## Step lemma: `i = 1` (requires `n.toNat ≥ 1`). -/
private theorem tri_at_step_one (n : u64)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_le : 1 ≤ n.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_129_tri.tri_at n 1 acc =
      clever_129_tri.tri_at n 2 (push_one acc 3 h_acc) := by
  conv => lhs; unfold clever_129_tri.tri_at
  have h_not_gt : ¬ (1 : u64) > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    rw [u64_one_toNat] at this; omega
  have h_dec_gt : decide ((1 : u64) > n) = false := decide_eq_false h_not_gt
  -- (1 ==? 0) is `pure false`.
  have h_eq0 : ((1 : u64) ==? (0 : u64) : RustM Bool) = pure false := by
    show pure ((1 : u64) == (0 : u64)) = pure false
    rfl
  -- (1 ==? 1) is `pure true`.
  have h_eq1 : ((1 : u64) ==? (1 : u64) : RustM Bool) = pure true := by
    show pure ((1 : u64) == (1 : u64)) = pure true
    rfl
  have h_add_one : ((1 : u64) +? (1 : u64) : RustM u64) = RustM.ok ((1 : u64) + 1) :=
    add_pure 1 1 (by rw [u64_one_toNat]; decide)
  have h_one_plus_one : ((1 : u64) + 1 : u64) = (2 : u64) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; decide)]
    rw [u64_one_toNat, u64_two_toNat]
  simp only [show ((1 : u64) >? n : RustM Bool) = pure (decide ((1 : u64) > n)) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_eq0, h_eq1]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[(3 : u64)] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(3 : u64)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[(3 : u64)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[(3 : u64)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc 3 h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind, h_add_one, h_one_plus_one]

/-! ## Step lemma: even `i ≥ 2`. -/

private theorem u64_div_two_toNat (d : u64) : (d / 2).toNat = d.toNat / 2 := by
  show (d / (2 : u64)).toNat = d.toNat / 2
  rw [UInt64.toNat_div]
  rw [u64_two_toNat]

private theorem u64_mod_two_toNat (d : u64) : (d % 2).toNat = d.toNat % 2 := by
  rw [UInt64.toNat_mod, u64_two_toNat]

private theorem tri_at_step_even (n i : u64)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_le : i.toNat ≤ n.toNat)
    (h_ge : 2 ≤ i.toNat)
    (h_even : i.toNat % 2 = 0)
    (h_fits : 1 + i.toNat / 2 < 2 ^ 64)
    (h_i_succ : i.toNat + 1 < 2 ^ 64)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_129_tri.tri_at n i acc =
      clever_129_tri.tri_at n (i + 1)
        (push_one acc (UInt64.ofNat (1 + i.toNat / 2)) h_acc) := by
  conv => lhs; unfold clever_129_tri.tri_at
  have h_not_gt : ¬ i > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt; omega
  have h_dec_gt : decide (i > n) = false := decide_eq_false h_not_gt
  have h_i_ne_0 : i ≠ (0 : u64) := by
    intro hh
    have : i.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_i_ne_1 : i ≠ (1 : u64) := by
    intro hh
    have : i.toNat = (1 : u64).toNat := by rw [hh]
    rw [u64_one_toNat] at this; omega
  have h_eq0_def : (i ==? (0 : u64) : RustM Bool) = pure (decide (i = (0 : u64))) := rfl
  have h_eq1_def : (i ==? (1 : u64) : RustM Bool) = pure (decide (i = (1 : u64))) := rfl
  have h_dec_eq0 : decide (i = (0 : u64)) = false := decide_eq_false h_i_ne_0
  have h_dec_eq1 : decide (i = (1 : u64)) = false := decide_eq_false h_i_ne_1
  have h_two_ne : (2 : u64) ≠ 0 := by
    intro hh
    have : (2 : u64).toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_two_toNat, u64_zero_toNat] at this; omega
  have h_mod : (i %? (2 : u64) : RustM u64) = pure (i % 2) := mod_pure i 2 h_two_ne
  have h_mod_zero : (i % 2 : u64) = 0 := by
    apply UInt64.toNat_inj.mp
    rw [u64_mod_two_toNat, u64_zero_toNat]
    exact h_even
  have h_eq_mod_def : ((i % 2) ==? (0 : u64) : RustM Bool) =
      pure (decide ((i % 2) = (0 : u64))) := rfl
  have h_dec_even : decide ((i % 2) = (0 : u64)) = true := decide_eq_true h_mod_zero
  have h_div : (i /? (2 : u64) : RustM u64) = pure (i / 2) := div_pure i 2 h_two_ne
  have h_div_toNat_lt : (i / 2).toNat < 2 ^ 64 := by
    rw [u64_div_two_toNat]
    have := UInt64.toNat_lt i
    omega
  have h_add_v : ((1 : u64) +? (i / 2) : RustM u64) = pure ((1 : u64) + (i / 2)) := by
    apply add_pure
    rw [u64_one_toNat, u64_div_two_toNat]; exact h_fits
  have h_v_toNat : ((1 : u64) + (i / 2)).toNat = 1 + i.toNat / 2 := by
    rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat, u64_div_two_toNat]; exact h_fits)]
    rw [u64_one_toNat, u64_div_two_toNat]
  have h_v_eq : (1 : u64) + (i / 2) = UInt64.ofNat (1 + i.toNat / 2) := by
    apply UInt64.toNat_inj.mp
    rw [h_v_toNat, UInt64.toNat_ofNat_of_lt' h_fits]
  have h_add_one : (i +? (1 : u64) : RustM u64) = RustM.ok (i + 1) :=
    add_pure i 1 (by rw [u64_one_toNat]; exact h_i_succ)
  simp only [show (i >? n : RustM Bool) = pure (decide (i > n)) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_eq0_def, h_dec_eq0, h_eq1_def, h_dec_eq1,
             h_mod, h_eq_mod_def, h_dec_even, h_div, h_add_v, h_v_eq, RustM_ok_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[UInt64.ofNat (1 + i.toNat / 2)] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[UInt64.ofNat (1 + i.toNat / 2)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[UInt64.ofNat (1 + i.toNat / 2)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[UInt64.ofNat (1 + i.toNat / 2)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc (UInt64.ofNat (1 + i.toNat / 2)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind, h_add_one]

/-! ## Step lemma: odd `i ≥ 3` — uses back-reference `acc[i-2]`. -/

private theorem u64_sub_toNat (d d' : u64) (h : d'.toNat ≤ d.toNat) :
    (d - d').toNat = d.toNat - d'.toNat := by
  have h_le : d' ≤ d := UInt64.le_iff_toNat_le.mpr h
  exact UInt64.toNat_sub_of_le d d' h_le

private theorem tri_at_step_odd (n i : u64)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_le : i.toNat ≤ n.toNat)
    (h_ge : 3 ≤ i.toNat)
    (h_odd : i.toNat % 2 = 1)
    (h_idx_bound : i.toNat - 2 < acc.val.size)
    (h_acc_at : (acc.val[i.toNat - 2]'h_idx_bound).toNat = tri_nat (i.toNat - 2))
    (h_po_fits : tri_nat (i.toNat - 2) < 2 ^ 64)
    (h_a_fits : 1 + (i.toNat - 1) / 2 < 2 ^ 64)
    (h_b_fits : 1 + (i.toNat + 1) / 2 < 2 ^ 64)
    (h_ab_po_fits : (1 + (i.toNat - 1) / 2) + tri_nat (i.toNat - 2) < 2 ^ 64)
    (h_v_fits : tri_nat i.toNat < 2 ^ 64)
    (h_i_succ : i.toNat + 1 < 2 ^ 64)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_129_tri.tri_at n i acc =
      clever_129_tri.tri_at n (i + 1)
        (push_one acc (UInt64.ofNat (tri_nat i.toNat)) h_acc) := by
  conv => lhs; unfold clever_129_tri.tri_at
  have h_not_gt : ¬ i > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt; omega
  have h_dec_gt : decide (i > n) = false := decide_eq_false h_not_gt
  have h_i_ne_0 : i ≠ (0 : u64) := by
    intro hh
    have : i.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_i_ne_1 : i ≠ (1 : u64) := by
    intro hh
    have : i.toNat = (1 : u64).toNat := by rw [hh]
    rw [u64_one_toNat] at this; omega
  have h_eq0_def : (i ==? (0 : u64) : RustM Bool) = pure (decide (i = (0 : u64))) := rfl
  have h_eq1_def : (i ==? (1 : u64) : RustM Bool) = pure (decide (i = (1 : u64))) := rfl
  have h_dec_eq0 : decide (i = (0 : u64)) = false := decide_eq_false h_i_ne_0
  have h_dec_eq1 : decide (i = (1 : u64)) = false := decide_eq_false h_i_ne_1
  have h_two_ne : (2 : u64) ≠ 0 := by
    intro hh
    have : (2 : u64).toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_two_toNat, u64_zero_toNat] at this; omega
  have h_mod : (i %? (2 : u64) : RustM u64) = pure (i % 2) := mod_pure i 2 h_two_ne
  have h_mod_ne : (i % 2 : u64) ≠ 0 := by
    intro hh
    have h_toNat : (i % 2 : u64).toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_mod_two_toNat, u64_zero_toNat] at h_toNat
    omega
  have h_eq_mod_def : ((i % 2) ==? (0 : u64) : RustM Bool) =
      pure (decide ((i % 2) = (0 : u64))) := rfl
  have h_dec_odd : decide ((i % 2) = (0 : u64)) = false := decide_eq_false h_mod_ne
  -- (i -? 2) = pure (i - 2).
  have h_sub_2 : (i -? (2 : u64) : RustM u64) = pure (i - 2) := by
    apply sub_pure
    rw [u64_two_toNat]; omega
  have h_sub_2_toNat : (i - 2).toNat = i.toNat - 2 := by
    rw [u64_sub_toNat]
    · rw [u64_two_toNat]
    · rw [u64_two_toNat]; omega
  -- cast (i - 2) to USize64.
  have h_cast :
      (rust_primitives.hax.cast_op (i - 2) : RustM USize64) =
        pure (UInt64.toUSize64 (i - 2)) := rfl
  have h_cast_toNat : (UInt64.toUSize64 (i - 2)).toNat = i.toNat - 2 := by
    show ((i - 2).toNat.toUSize64).toNat = i.toNat - 2
    rw [USize64.toNat_ofNat_of_lt'
        (by rw [usize_size_eq_2_64, h_sub_2_toNat]; have := UInt64.toNat_lt i; omega)]
    exact h_sub_2_toNat
  -- acc[USize64.ofNat (i-2)]_?
  have h_idx_lt : (UInt64.toUSize64 (i - 2)).toNat < acc.val.size := by
    rw [h_cast_toNat]; exact h_idx_bound
  have h_lookup :
      (acc[UInt64.toUSize64 (i - 2)]_? : RustM u64) =
        RustM.ok (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt) := by
    show (if h : (UInt64.toUSize64 (i - 2)).toNat < acc.val.size
            then pure (acc.val[UInt64.toUSize64 (i - 2)]) else .fail .arrayOutOfBounds)
        = RustM.ok (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)
    rw [dif_pos h_idx_lt]
    rfl
  -- The prev_odd value.
  have h_prev_odd_toNat :
      (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt).toNat = tri_nat (i.toNat - 2) := by
    have h_eq : (UInt64.toUSize64 (i - 2)).toNat = i.toNat - 2 := h_cast_toNat
    have h_get_eq : acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt
            = acc.val[i.toNat - 2]'h_idx_bound := by
      congr 1
    rw [h_get_eq]; exact h_acc_at
  -- (i -? 1) = pure (i - 1).
  have h_sub_1 : (i -? (1 : u64) : RustM u64) = pure (i - 1) := by
    apply sub_pure
    rw [u64_one_toNat]; omega
  have h_sub_1_toNat : (i - 1).toNat = i.toNat - 1 := by
    rw [u64_sub_toNat]
    · rw [u64_one_toNat]
    · rw [u64_one_toNat]; omega
  -- ((i-1) /? 2) = pure ((i-1) / 2).
  have h_div_m1 : ((i - 1) /? (2 : u64) : RustM u64) = pure ((i - 1) / 2) := div_pure _ _ h_two_ne
  have h_div_m1_toNat : ((i - 1) / 2).toNat = (i.toNat - 1) / 2 := by
    rw [u64_div_two_toNat, h_sub_1_toNat]
  -- a = 1 + (i-1)/2.
  have h_a_pure : ((1 : u64) +? ((i - 1) / 2) : RustM u64) = pure ((1 : u64) + ((i - 1) / 2)) := by
    apply add_pure
    rw [u64_one_toNat, h_div_m1_toNat]; exact h_a_fits
  have h_a_toNat : ((1 : u64) + ((i - 1) / 2)).toNat = 1 + (i.toNat - 1) / 2 := by
    rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat, h_div_m1_toNat]; exact h_a_fits)]
    rw [u64_one_toNat, h_div_m1_toNat]
  -- (i +? 1) = pure (i + 1).
  have h_add_one_pure : (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
    apply add_pure
    rw [u64_one_toNat]; exact h_i_succ
  have h_add_one_toNat : (i + 1).toNat = i.toNat + 1 := succ_toNat i h_i_succ
  -- ((i+1) /? 2) = pure ((i+1)/2).
  have h_div_p1 : ((i + 1) /? (2 : u64) : RustM u64) = pure ((i + 1) / 2) :=
    div_pure _ _ h_two_ne
  have h_div_p1_toNat : ((i + 1) / 2).toNat = (i.toNat + 1) / 2 := by
    rw [u64_div_two_toNat, h_add_one_toNat]
  -- b = 1 + (i+1)/2.
  have h_b_pure : ((1 : u64) +? ((i + 1) / 2) : RustM u64) = pure ((1 : u64) + ((i + 1) / 2)) := by
    apply add_pure
    rw [u64_one_toNat, h_div_p1_toNat]; exact h_b_fits
  have h_b_toNat : ((1 : u64) + ((i + 1) / 2)).toNat = 1 + (i.toNat + 1) / 2 := by
    rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat, h_div_p1_toNat]; exact h_b_fits)]
    rw [u64_one_toNat, h_div_p1_toNat]
  -- Compute the intermediate fits/values directly on the inlined expressions.
  have h_a_plus_po_fits :
      ((1 : u64) + ((i - 1) / 2)).toNat
        + (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt).toNat < 2 ^ 64 := by
    rw [h_a_toNat, h_prev_odd_toNat]
    exact h_ab_po_fits
  have h_a_plus_po_pure :
      (((1 : u64) + ((i - 1) / 2)) +?
        (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt) : RustM u64) =
      pure (((1 : u64) + ((i - 1) / 2)) +
            (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)) :=
    add_pure _ _ h_a_plus_po_fits
  have h_a_plus_po_toNat :
      (((1 : u64) + ((i - 1) / 2)) +
        (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)).toNat =
        (1 + (i.toNat - 1) / 2) + tri_nat (i.toNat - 2) := by
    rw [UInt64.toNat_add_of_lt h_a_plus_po_fits, h_a_toNat, h_prev_odd_toNat]
  have h_full_fits :
      (((1 : u64) + ((i - 1) / 2)) +
        (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)).toNat
        + ((1 : u64) + ((i + 1) / 2)).toNat < 2 ^ 64 := by
    rw [h_a_plus_po_toNat, h_b_toNat]
    have h_recur : tri_nat i.toNat =
        1 + (i.toNat - 1) / 2 + tri_nat (i.toNat - 2) + 1 + (i.toNat + 1) / 2 :=
      tri_nat_odd i.toNat h_ge h_odd
    omega
  have h_full_pure :
      ((((1 : u64) + ((i - 1) / 2)) +
         (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt))
        +? ((1 : u64) + ((i + 1) / 2)) : RustM u64) =
      pure ((((1 : u64) + ((i - 1) / 2)) +
              (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)) +
              ((1 : u64) + ((i + 1) / 2))) :=
    add_pure _ _ h_full_fits
  have h_full_toNat :
      ((((1 : u64) + ((i - 1) / 2)) +
         (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)) +
          ((1 : u64) + ((i + 1) / 2))).toNat = tri_nat i.toNat := by
    rw [UInt64.toNat_add_of_lt h_full_fits, h_a_plus_po_toNat, h_b_toNat]
    have h_recur : tri_nat i.toNat =
        1 + (i.toNat - 1) / 2 + tri_nat (i.toNat - 2) + 1 + (i.toNat + 1) / 2 :=
      tri_nat_odd i.toNat h_ge h_odd
    omega
  have h_v_eq :
      (((1 : u64) + ((i - 1) / 2)) +
         (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)) +
          ((1 : u64) + ((i + 1) / 2)) = UInt64.ofNat (tri_nat i.toNat) := by
    apply UInt64.toNat_inj.mp
    rw [h_full_toNat, UInt64.toNat_ofNat_of_lt' h_v_fits]
  -- Now reduce.
  simp only [show (i >? n : RustM Bool) = pure (decide (i > n)) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_eq0_def, h_dec_eq0, h_eq1_def, h_dec_eq1,
             h_mod, h_eq_mod_def, h_dec_odd,
             h_sub_2, h_cast, h_lookup, RustM_ok_bind,
             h_sub_1, h_div_m1, h_a_pure,
             h_add_one_pure, h_div_p1, h_b_pure,
             h_a_plus_po_pure, h_full_pure, h_v_eq]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[UInt64.ofNat (tri_nat i.toNat)] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[UInt64.ofNat (tri_nat i.toNat)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[UInt64.ofNat (tri_nat i.toNat)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[UInt64.ofNat (tri_nat i.toNat)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc (UInt64.ofNat (tri_nat i.toNat)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind, h_add_one_pure]

/-! ## Failure step lemma: odd `i ≥ 3` where `a +? prev_odd` overflows. -/

private theorem tri_at_step_odd_fails_ab_po (n i : u64)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_le : i.toNat ≤ n.toNat)
    (h_ge : 3 ≤ i.toNat)
    (h_odd : i.toNat % 2 = 1)
    (h_idx_bound : i.toNat - 2 < acc.val.size)
    (h_acc_at : (acc.val[i.toNat - 2]'h_idx_bound).toNat = tri_nat (i.toNat - 2))
    (h_po_fits : tri_nat (i.toNat - 2) < 2 ^ 64)
    (h_a_fits : 1 + (i.toNat - 1) / 2 < 2 ^ 64)
    (h_b_fits : 1 + (i.toNat + 1) / 2 < 2 ^ 64)
    (h_ab_po_overflow : 2 ^ 64 ≤ (1 + (i.toNat - 1) / 2) + tri_nat (i.toNat - 2))
    (h_i_succ : i.toNat + 1 < 2 ^ 64) :
    clever_129_tri.tri_at n i acc = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_129_tri.tri_at
  have h_not_gt : ¬ i > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt; omega
  have h_dec_gt : decide (i > n) = false := decide_eq_false h_not_gt
  have h_i_ne_0 : i ≠ (0 : u64) := by
    intro hh
    have : i.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_i_ne_1 : i ≠ (1 : u64) := by
    intro hh
    have : i.toNat = (1 : u64).toNat := by rw [hh]
    rw [u64_one_toNat] at this; omega
  have h_eq0_def : (i ==? (0 : u64) : RustM Bool) = pure (decide (i = (0 : u64))) := rfl
  have h_eq1_def : (i ==? (1 : u64) : RustM Bool) = pure (decide (i = (1 : u64))) := rfl
  have h_dec_eq0 : decide (i = (0 : u64)) = false := decide_eq_false h_i_ne_0
  have h_dec_eq1 : decide (i = (1 : u64)) = false := decide_eq_false h_i_ne_1
  have h_two_ne : (2 : u64) ≠ 0 := by
    intro hh
    have : (2 : u64).toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_two_toNat, u64_zero_toNat] at this; omega
  have h_mod : (i %? (2 : u64) : RustM u64) = pure (i % 2) := mod_pure i 2 h_two_ne
  have h_mod_ne : (i % 2 : u64) ≠ 0 := by
    intro hh
    have h_toNat : (i % 2 : u64).toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_mod_two_toNat, u64_zero_toNat] at h_toNat
    omega
  have h_eq_mod_def : ((i % 2) ==? (0 : u64) : RustM Bool) =
      pure (decide ((i % 2) = (0 : u64))) := rfl
  have h_dec_odd : decide ((i % 2) = (0 : u64)) = false := decide_eq_false h_mod_ne
  have h_sub_2 : (i -? (2 : u64) : RustM u64) = pure (i - 2) := by
    apply sub_pure
    rw [u64_two_toNat]; omega
  have h_sub_2_toNat : (i - 2).toNat = i.toNat - 2 := by
    rw [u64_sub_toNat]
    · rw [u64_two_toNat]
    · rw [u64_two_toNat]; omega
  have h_cast :
      (rust_primitives.hax.cast_op (i - 2) : RustM USize64) =
        pure (UInt64.toUSize64 (i - 2)) := rfl
  have h_cast_toNat : (UInt64.toUSize64 (i - 2)).toNat = i.toNat - 2 := by
    show ((i - 2).toNat.toUSize64).toNat = i.toNat - 2
    rw [USize64.toNat_ofNat_of_lt'
        (by rw [usize_size_eq_2_64, h_sub_2_toNat]; have := UInt64.toNat_lt i; omega)]
    exact h_sub_2_toNat
  have h_idx_lt : (UInt64.toUSize64 (i - 2)).toNat < acc.val.size := by
    rw [h_cast_toNat]; exact h_idx_bound
  have h_lookup :
      (acc[UInt64.toUSize64 (i - 2)]_? : RustM u64) =
        RustM.ok (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt) := by
    show (if h : (UInt64.toUSize64 (i - 2)).toNat < acc.val.size
            then pure (acc.val[UInt64.toUSize64 (i - 2)]) else .fail .arrayOutOfBounds)
        = RustM.ok (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt)
    rw [dif_pos h_idx_lt]
    rfl
  have h_prev_odd_toNat :
      (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt).toNat = tri_nat (i.toNat - 2) := by
    have h_get_eq : acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt
            = acc.val[i.toNat - 2]'h_idx_bound := by
      congr 1
    rw [h_get_eq]; exact h_acc_at
  have h_sub_1 : (i -? (1 : u64) : RustM u64) = pure (i - 1) := by
    apply sub_pure
    rw [u64_one_toNat]; omega
  have h_sub_1_toNat : (i - 1).toNat = i.toNat - 1 := by
    rw [u64_sub_toNat]
    · rw [u64_one_toNat]
    · rw [u64_one_toNat]; omega
  have h_div_m1 : ((i - 1) /? (2 : u64) : RustM u64) = pure ((i - 1) / 2) := div_pure _ _ h_two_ne
  have h_div_m1_toNat : ((i - 1) / 2).toNat = (i.toNat - 1) / 2 := by
    rw [u64_div_two_toNat, h_sub_1_toNat]
  have h_a_pure : ((1 : u64) +? ((i - 1) / 2) : RustM u64) = pure ((1 : u64) + ((i - 1) / 2)) := by
    apply add_pure
    rw [u64_one_toNat, h_div_m1_toNat]; exact h_a_fits
  have h_a_toNat : ((1 : u64) + ((i - 1) / 2)).toNat = 1 + (i.toNat - 1) / 2 := by
    rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat, h_div_m1_toNat]; exact h_a_fits)]
    rw [u64_one_toNat, h_div_m1_toNat]
  have h_add_one_pure : (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
    apply add_pure
    rw [u64_one_toNat]; exact h_i_succ
  have h_div_p1 : ((i + 1) /? (2 : u64) : RustM u64) = pure ((i + 1) / 2) :=
    div_pure _ _ h_two_ne
  have h_div_p1_toNat : ((i + 1) / 2).toNat = (i.toNat + 1) / 2 := by
    rw [u64_div_two_toNat, succ_toNat i h_i_succ]
  have h_b_pure : ((1 : u64) +? ((i + 1) / 2) : RustM u64) = pure ((1 : u64) + ((i + 1) / 2)) := by
    apply add_pure
    rw [u64_one_toNat, h_div_p1_toNat]; exact h_b_fits
  -- Overflow at `a +? prev_odd`.
  have h_a_plus_po_overflow :
      2 ^ 64 ≤ ((1 : u64) + ((i - 1) / 2)).toNat
                + (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt).toNat := by
    rw [h_a_toNat, h_prev_odd_toNat]
    exact h_ab_po_overflow
  have h_a_plus_po_fail :
      (((1 : u64) + ((i - 1) / 2)) +?
        (acc.val[(UInt64.toUSize64 (i - 2)).toNat]'h_idx_lt) : RustM u64) =
      .fail .integerOverflow :=
    add_fail _ _ h_a_plus_po_overflow
  -- Now reduce.
  simp only [show (i >? n : RustM Bool) = pure (decide (i > n)) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_eq0_def, h_dec_eq0, h_eq1_def, h_dec_eq1,
             h_mod, h_eq_mod_def, h_dec_odd,
             h_sub_2, h_cast, h_lookup, RustM_ok_bind,
             h_sub_1, h_div_m1, h_a_pure,
             h_add_one_pure, h_div_p1, h_b_pure,
             h_a_plus_po_fail]
  rfl

/-! ## Auxiliary bounds for tri_nat at sub-arguments used in the odd step. -/

/-- For odd `i ≤ N_bound` with `i ≥ 3`, the intermediate `1 + (i-1)/2 + tri_nat(i-2)`
    is bounded by `tri_nat i` (which fits). -/
private theorem tri_nat_ab_po_le (i : Nat) (h_le : i ≤ N_bound)
    (h_ge : 3 ≤ i) (h_odd : i % 2 = 1) :
    1 + (i - 1) / 2 + tri_nat (i - 2) < 2 ^ 64 := by
  have h_recur : tri_nat i = 1 + (i - 1) / 2 + tri_nat (i - 2) + 1 + (i + 1) / 2 :=
    tri_nat_odd i h_ge h_odd
  have h_tri_lt : tri_nat i < 2 ^ 64 := tri_nat_lt_2_64 i h_le
  omega

/-! ## Strong-induction bounded correctness. -/

private theorem tri_at_correct (n : u64) (hn : n.toNat ≤ N_bound) :
    ∀ (m : Nat) (i : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      n.toNat + 1 - i.toNat ≤ m →
      i.toNat ≤ n.toNat + 1 →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size),
          (acc.val[j]'hj).toNat = tri_nat j) →
      ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
        clever_129_tri.tri_at n i acc = RustM.ok v ∧
        v.val.size = n.toNat + 1 ∧
        (∀ (j : Nat) (hj : j < v.val.size),
            (v.val[j]'hj).toNat = tri_nat j) := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le h_acc_size h_acc_inv
    have hi_eq : i.toNat = n.toNat + 1 := by omega
    have h_oob : n.toNat < i.toNat := by omega
    refine ⟨acc, tri_at_oob n i acc h_oob, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro j hj; exact h_acc_inv j hj
  | succ m ih =>
    intro i acc hm hi_le h_acc_size h_acc_inv
    by_cases hi_top : i.toNat = n.toNat + 1
    · have h_oob : n.toNat < i.toNat := by omega
      refine ⟨acc, tri_at_oob n i acc h_oob, ?_, ?_⟩
      · rw [h_acc_size, hi_top]
      · intro j hj; exact h_acc_inv j hj
    · -- i.toNat ≤ n.toNat
      have hi_le_n : i.toNat ≤ n.toNat := by omega
      have hi_le_N : i.toNat ≤ N_bound := by omega
      have h_acc_room : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, usize_size_eq_2_64]
        have h_n_lt : n.toNat + 1 < 2 ^ 64 := by
          have : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
          omega
        omega
      have h_i_succ_fits : i.toNat + 1 < 2 ^ 64 := by
        have h_n_lt : n.toNat + 1 < 2 ^ 64 := by
          have : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
          omega
        omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := succ_toNat i h_i_succ_fits
      have h_meas : n.toNat + 1 - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      have h_i1_le : (i + 1).toNat ≤ n.toNat + 1 := by rw [h_i1_toNat]; omega
      -- Case-split on i.toNat: 0, 1, even≥2, odd≥3.
      by_cases hi0 : i.toNat = 0
      · -- i = 0 case.
        have h_i_eq_zero : i = (0 : u64) := UInt64.toNat_inj.mp (by rw [hi0, u64_zero_toNat])
        subst h_i_eq_zero
        have h_step := tri_at_step_zero n acc h_acc_room
        -- Need: acc.val.size = 0, so push_one acc 3 has size 1.
        have h_acc_zero : acc.val.size = 0 := by rw [h_acc_size, u64_zero_toNat]
        have h_acc'_size : (push_one acc 3 h_acc_room).val.size = (0 + 1 : u64).toNat := by
          rw [push_one_size]
          show acc.val.size + 1 = ((0 : u64) + 1).toNat
          rw [h_acc_zero, succ_toNat 0 (by rw [u64_zero_toNat]; decide)]
          rw [u64_zero_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc 3 h_acc_room).val.size),
              ((push_one acc 3 h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc 3 h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have h_size_app : (acc.val ++ #[(3 : u64)]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_in : j < acc.val.size + 1 := by
              show j < acc.val.size + 1
              have := push_one_size acc 3 h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc 3 h_acc_room hj]
            rw [u64_three_toNat, h_acc_zero, tri_nat_zero]
        rw [h_step]
        exact ih (0 + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv
      by_cases hi1 : i.toNat = 1
      · -- i = 1 case.
        have h_i_eq_one : i = (1 : u64) := UInt64.toNat_inj.mp (by rw [hi1, u64_one_toNat])
        subst h_i_eq_one
        have h_n_ge_1 : 1 ≤ n.toNat := by rw [u64_one_toNat] at hi_le_n; exact hi_le_n
        have h_step := tri_at_step_one n acc h_n_ge_1 h_acc_room
        have h_acc_one : acc.val.size = 1 := by rw [h_acc_size, u64_one_toNat]
        have h_acc'_size : (push_one acc 3 h_acc_room).val.size = (1 + 1 : u64).toNat := by
          rw [push_one_size]
          show acc.val.size + 1 = ((1 : u64) + 1).toNat
          rw [h_acc_one, succ_toNat 1 (by rw [u64_one_toNat]; decide)]
          rw [u64_one_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc 3 h_acc_room).val.size),
              ((push_one acc 3 h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc 3 h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj_in : j < acc.val.size + 1 := by
              have := push_one_size acc 3 h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc 3 h_acc_room hj]
            rw [u64_three_toNat, h_acc_one, tri_nat_one]
        rw [h_step]
        exact ih (1 + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv
      have hi_ge_2 : 2 ≤ i.toNat := by omega
      rcases Nat.mod_two_eq_zero_or_one i.toNat with h_par | h_par
      · -- Even branch.
        have h_v_fits_even : 1 + i.toNat / 2 < 2 ^ 64 := by
          have h_tri_even := tri_nat_even_lt i.toNat hi_le_N h_par hi_ge_2
          rw [tri_nat_even _ hi_ge_2 h_par] at h_tri_even
          exact h_tri_even
        have h_step := tri_at_step_even n i acc hi_le_n hi_ge_2 h_par
                          h_v_fits_even h_i_succ_fits h_acc_room
        let v_pushed : u64 := UInt64.ofNat (1 + i.toNat / 2)
        have h_v_toNat : v_pushed.toNat = 1 + i.toNat / 2 :=
          UInt64.toNat_ofNat_of_lt' h_v_fits_even
        have h_v_eq_tri : v_pushed.toNat = tri_nat i.toNat := by
          rw [h_v_toNat]
          exact (tri_nat_even _ hi_ge_2 h_par).symm
        have h_acc'_size : (push_one acc v_pushed h_acc_room).val.size = (i + 1).toNat := by
          rw [push_one_size, h_acc_size, h_i1_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc v_pushed h_acc_room).val.size),
              ((push_one acc v_pushed h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc v_pushed h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj' : j < acc.val.size + 1 := by
              have := push_one_size acc v_pushed h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc v_pushed h_acc_room hj]
            rw [h_acc_size]
            exact h_v_eq_tri
        rw [h_step]
        exact ih (i + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv
      · -- Odd branch (≥ 3).
        have hi_ge_3 : 3 ≤ i.toNat := by omega
        have h_v_fits_odd : tri_nat i.toNat < 2 ^ 64 := tri_nat_lt_2_64 i.toNat hi_le_N
        -- a fits.
        have h_a_fits : 1 + (i.toNat - 1) / 2 < 2 ^ 64 := by
          have : (i.toNat - 1) / 2 ≤ N_bound := by
            have h1 : i.toNat - 1 ≤ N_bound := by omega
            have h2 : (i.toNat - 1) / 2 ≤ i.toNat - 1 := Nat.div_le_self _ _
            omega
          have h_n : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
          omega
        -- b fits.
        have h_b_fits : 1 + (i.toNat + 1) / 2 < 2 ^ 64 := by
          have h_i_le : i.toNat + 1 ≤ N_bound + 1 := by omega
          have h_div_le : (i.toNat + 1) / 2 ≤ (N_bound + 1) / 2 :=
            Nat.div_le_div_right h_i_le
          have h_N_div : (N_bound + 1) / 2 ≤ N_bound + 1 := Nat.div_le_self _ _
          have h_N : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
          omega
        -- prev_odd fits.
        have h_po_fits : tri_nat (i.toNat - 2) < 2 ^ 64 := by
          apply tri_nat_lt_2_64
          omega
        -- a + po fits.
        have h_ab_po_fits :
            (1 + (i.toNat - 1) / 2) + tri_nat (i.toNat - 2) < 2 ^ 64 :=
          tri_nat_ab_po_le i.toNat hi_le_N hi_ge_3 h_par
        -- idx bound.
        have h_idx_bound : i.toNat - 2 < acc.val.size := by
          rw [h_acc_size]; omega
        have h_acc_at : (acc.val[i.toNat - 2]'h_idx_bound).toNat = tri_nat (i.toNat - 2) :=
          h_acc_inv (i.toNat - 2) h_idx_bound
        have h_step := tri_at_step_odd n i acc hi_le_n hi_ge_3 h_par
                          h_idx_bound h_acc_at h_po_fits h_a_fits h_b_fits h_ab_po_fits
                          h_v_fits_odd h_i_succ_fits h_acc_room
        let v_pushed : u64 := UInt64.ofNat (tri_nat i.toNat)
        have h_v_toNat : v_pushed.toNat = tri_nat i.toNat :=
          UInt64.toNat_ofNat_of_lt' h_v_fits_odd
        have h_acc'_size : (push_one acc v_pushed h_acc_room).val.size = (i + 1).toNat := by
          rw [push_one_size, h_acc_size, h_i1_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc v_pushed h_acc_room).val.size),
              ((push_one acc v_pushed h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc v_pushed h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj' : j < acc.val.size + 1 := by
              have := push_one_size acc v_pushed h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc v_pushed h_acc_room hj]
            rw [h_acc_size]
            exact h_v_toNat
        rw [h_step]
        exact ih (i + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv

/-! ## Failure induction: for `n.toNat ≥ N_bound + 1`, the iteration starting
    from an invariant-respecting accumulator at `i ≤ N_bound + 1` must fail. -/

/-- Bound: at `i.toNat = N_bound + 1`, all the side conditions for the
    failure step lemma hold. -/
private theorem tri_at_overflow_at_target (n : u64) (h_n_large : N_bound + 1 ≤ n.toNat)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_size : acc.val.size = N_bound + 1)
    (h_inv : ∀ (j : Nat) (hj : j < acc.val.size), (acc.val[j]'hj).toNat = tri_nat j) :
    clever_129_tri.tri_at n (UInt64.ofNat (N_bound + 1)) acc = RustM.fail .integerOverflow := by
  have h_target_lt_2_64 : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
  have h_i_eq : (UInt64.ofNat (N_bound + 1) : u64).toNat = N_bound + 1 :=
    UInt64.toNat_ofNat_of_lt' h_target_lt_2_64
  have h_idx_bound : (UInt64.ofNat (N_bound + 1) : u64).toNat - 2 < acc.val.size := by
    rw [h_size, h_i_eq]
    rw [N_bound_eq]; decide
  have h_acc_at : (acc.val[(UInt64.ofNat (N_bound + 1) : u64).toNat - 2]'h_idx_bound).toNat
                    = tri_nat ((UInt64.ofNat (N_bound + 1) : u64).toNat - 2) :=
    h_inv ((UInt64.ofNat (N_bound + 1) : u64).toNat - 2) h_idx_bound
  -- Numeric facts at i.toNat = N_bound + 1.
  have h_le_n : (UInt64.ofNat (N_bound + 1) : u64).toNat ≤ n.toNat := by rw [h_i_eq]; exact h_n_large
  have h_ge_3 : 3 ≤ (UInt64.ofNat (N_bound + 1) : u64).toNat := by
    rw [h_i_eq, N_bound_eq]; decide
  have h_odd : (UInt64.ofNat (N_bound + 1) : u64).toNat % 2 = 1 := by
    rw [h_i_eq, N_bound_eq]
  have h_po_fits :
      tri_nat ((UInt64.ofNat (N_bound + 1) : u64).toNat - 2) < 2 ^ 64 := by
    apply tri_nat_lt_2_64
    rw [h_i_eq, N_bound_eq]; decide
  have h_a_fits :
      1 + ((UInt64.ofNat (N_bound + 1) : u64).toNat - 1) / 2 < 2 ^ 64 := by
    rw [h_i_eq, N_bound_eq]; decide
  have h_b_fits :
      1 + ((UInt64.ofNat (N_bound + 1) : u64).toNat + 1) / 2 < 2 ^ 64 := by
    rw [h_i_eq, N_bound_eq]; decide
  have h_ab_po_overflow :
      2 ^ 64 ≤ (1 + ((UInt64.ofNat (N_bound + 1) : u64).toNat - 1) / 2)
                + tri_nat ((UInt64.ofNat (N_bound + 1) : u64).toNat - 2) := by
    rw [h_i_eq]
    -- Need: 2^64 ≤ (1 + (N_bound + 1 - 1)/2) + tri_nat (N_bound + 1 - 2)
    --     = (1 + N_bound/2) + tri_nat (N_bound - 1)
    -- N_bound = 2^33 - 2; N_bound/2 = 2^32 - 1; 1 + N_bound/2 = 2^32.
    -- N_bound - 1 = 2^33 - 3; (k+1)(k+3) with k = (N-3)/2 = 2^32 - 2.
    --   = (2^32 - 1)(2^32 + 1) = 2^64 - 1.
    -- Sum = 2^32 + 2^64 - 1 ≥ 2^64.
    have h_lhs1 : 1 + (N_bound + 1 - 1) / 2 = 2 ^ 32 := by rw [N_bound_eq]
    have h_tri_eq : tri_nat (N_bound + 1 - 2) = 2 ^ 64 - 1 := by
      rw [show N_bound + 1 - 2 = 2 * (2 ^ 32 - 2) + 1 from by rw [N_bound_eq]]
      rw [tri_nat_odd_closed_form]
    rw [h_lhs1, h_tri_eq]
    decide
  have h_i_succ_fits : (UInt64.ofNat (N_bound + 1) : u64).toNat + 1 < 2 ^ 64 := by
    rw [h_i_eq, N_bound_eq]; decide
  exact tri_at_step_odd_fails_ab_po n (UInt64.ofNat (N_bound + 1)) acc
          h_le_n h_ge_3 h_odd h_idx_bound h_acc_at h_po_fits h_a_fits h_b_fits
          h_ab_po_overflow h_i_succ_fits

/-! ## Strong-induction failure proof. -/

private theorem tri_at_fails (n : u64) (h_n_large : N_bound + 1 ≤ n.toNat) :
    ∀ (m : Nat) (i : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      N_bound + 1 - i.toNat ≤ m →
      i.toNat ≤ N_bound + 1 →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size), (acc.val[j]'hj).toNat = tri_nat j) →
      ∃ e, clever_129_tri.tri_at n i acc = RustM.fail e := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le h_acc_size h_acc_inv
    have hi_eq : i.toNat = N_bound + 1 := by omega
    have h_i_eq_u : i = UInt64.ofNat (N_bound + 1) := by
      apply UInt64.toNat_inj.mp
      rw [hi_eq, UInt64.toNat_ofNat_of_lt' N_bound_lt_2_64]
    rw [h_i_eq_u]
    refine ⟨.integerOverflow, ?_⟩
    apply tri_at_overflow_at_target n h_n_large acc _ _
    · exact h_acc_size.trans hi_eq
    · intro j hj; exact h_acc_inv j hj
  | succ m ih =>
    intro i acc hm hi_le h_acc_size h_acc_inv
    by_cases hi_top : i.toNat = N_bound + 1
    · have h_i_eq_u : i = UInt64.ofNat (N_bound + 1) := by
        apply UInt64.toNat_inj.mp
        rw [hi_top, UInt64.toNat_ofNat_of_lt' N_bound_lt_2_64]
      rw [h_i_eq_u]
      refine ⟨.integerOverflow, ?_⟩
      apply tri_at_overflow_at_target n h_n_large acc _ _
      · exact h_acc_size.trans hi_top
      · intro j hj; exact h_acc_inv j hj
    · -- i.toNat ≤ N_bound
      have hi_le_N : i.toNat ≤ N_bound := by omega
      have hi_le_n : i.toNat ≤ n.toNat := by omega
      have h_acc_room : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, usize_size_eq_2_64]
        have : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
        omega
      have h_i_succ_fits : i.toNat + 1 < 2 ^ 64 := by
        have : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
        omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := succ_toNat i h_i_succ_fits
      have h_meas : N_bound + 1 - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
      have h_i1_le : (i + 1).toNat ≤ N_bound + 1 := by rw [h_i1_toNat]; omega
      by_cases hi0 : i.toNat = 0
      · have h_i_eq_zero : i = (0 : u64) := UInt64.toNat_inj.mp (by rw [hi0, u64_zero_toNat])
        subst h_i_eq_zero
        have h_step := tri_at_step_zero n acc h_acc_room
        have h_acc_zero : acc.val.size = 0 := by rw [h_acc_size, u64_zero_toNat]
        have h_acc'_size : (push_one acc 3 h_acc_room).val.size = (0 + 1 : u64).toNat := by
          rw [push_one_size]
          rw [h_acc_zero, succ_toNat 0 (by rw [u64_zero_toNat]; decide), u64_zero_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc 3 h_acc_room).val.size),
              ((push_one acc 3 h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc 3 h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj_in : j < acc.val.size + 1 := by
              have := push_one_size acc 3 h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc 3 h_acc_room hj]
            rw [u64_three_toNat, h_acc_zero, tri_nat_zero]
        rw [h_step]
        exact ih (0 + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv
      by_cases hi1 : i.toNat = 1
      · have h_i_eq_one : i = (1 : u64) := UInt64.toNat_inj.mp (by rw [hi1, u64_one_toNat])
        subst h_i_eq_one
        have h_n_ge_1 : 1 ≤ n.toNat := by rw [u64_one_toNat] at hi_le_n; exact hi_le_n
        have h_step := tri_at_step_one n acc h_n_ge_1 h_acc_room
        have h_acc_one : acc.val.size = 1 := by rw [h_acc_size, u64_one_toNat]
        have h_acc'_size : (push_one acc 3 h_acc_room).val.size = (1 + 1 : u64).toNat := by
          rw [push_one_size, h_acc_one,
              succ_toNat 1 (by rw [u64_one_toNat]; decide), u64_one_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc 3 h_acc_room).val.size),
              ((push_one acc 3 h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc 3 h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj_in : j < acc.val.size + 1 := by
              have := push_one_size acc 3 h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc 3 h_acc_room hj]
            rw [u64_three_toNat, h_acc_one, tri_nat_one]
        rw [h_step]
        exact ih (1 + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv
      have hi_ge_2 : 2 ≤ i.toNat := by omega
      rcases Nat.mod_two_eq_zero_or_one i.toNat with h_par | h_par
      · have h_v_fits_even : 1 + i.toNat / 2 < 2 ^ 64 := by
          have h_tri_even := tri_nat_even_lt i.toNat hi_le_N h_par hi_ge_2
          rw [tri_nat_even _ hi_ge_2 h_par] at h_tri_even
          exact h_tri_even
        have h_step := tri_at_step_even n i acc hi_le_n hi_ge_2 h_par
                          h_v_fits_even h_i_succ_fits h_acc_room
        let v_pushed : u64 := UInt64.ofNat (1 + i.toNat / 2)
        have h_v_toNat : v_pushed.toNat = 1 + i.toNat / 2 :=
          UInt64.toNat_ofNat_of_lt' h_v_fits_even
        have h_v_eq_tri : v_pushed.toNat = tri_nat i.toNat := by
          rw [h_v_toNat]
          exact (tri_nat_even _ hi_ge_2 h_par).symm
        have h_acc'_size : (push_one acc v_pushed h_acc_room).val.size = (i + 1).toNat := by
          rw [push_one_size, h_acc_size, h_i1_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc v_pushed h_acc_room).val.size),
              ((push_one acc v_pushed h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc v_pushed h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj' : j < acc.val.size + 1 := by
              have := push_one_size acc v_pushed h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc v_pushed h_acc_room hj]
            rw [h_acc_size]
            exact h_v_eq_tri
        rw [h_step]
        exact ih (i + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv
      · have hi_ge_3 : 3 ≤ i.toNat := by omega
        have h_v_fits_odd : tri_nat i.toNat < 2 ^ 64 := tri_nat_lt_2_64 i.toNat hi_le_N
        have h_a_fits : 1 + (i.toNat - 1) / 2 < 2 ^ 64 := by
          have : (i.toNat - 1) / 2 ≤ N_bound := by
            have h1 : i.toNat - 1 ≤ N_bound := by omega
            have h2 : (i.toNat - 1) / 2 ≤ i.toNat - 1 := Nat.div_le_self _ _
            omega
          have h_n : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
          omega
        have h_b_fits : 1 + (i.toNat + 1) / 2 < 2 ^ 64 := by
          have h_i_le : i.toNat + 1 ≤ N_bound + 1 := by omega
          have h_div_le : (i.toNat + 1) / 2 ≤ (N_bound + 1) / 2 :=
            Nat.div_le_div_right h_i_le
          have h_N_div : (N_bound + 1) / 2 ≤ N_bound + 1 := Nat.div_le_self _ _
          have h_N : N_bound + 1 < 2 ^ 64 := N_bound_lt_2_64
          omega
        have h_po_fits : tri_nat (i.toNat - 2) < 2 ^ 64 := by
          apply tri_nat_lt_2_64
          omega
        have h_ab_po_fits :
            (1 + (i.toNat - 1) / 2) + tri_nat (i.toNat - 2) < 2 ^ 64 :=
          tri_nat_ab_po_le i.toNat hi_le_N hi_ge_3 h_par
        have h_idx_bound : i.toNat - 2 < acc.val.size := by
          rw [h_acc_size]; omega
        have h_acc_at : (acc.val[i.toNat - 2]'h_idx_bound).toNat = tri_nat (i.toNat - 2) :=
          h_acc_inv (i.toNat - 2) h_idx_bound
        have h_step := tri_at_step_odd n i acc hi_le_n hi_ge_3 h_par
                          h_idx_bound h_acc_at h_po_fits h_a_fits h_b_fits h_ab_po_fits
                          h_v_fits_odd h_i_succ_fits h_acc_room
        let v_pushed : u64 := UInt64.ofNat (tri_nat i.toNat)
        have h_v_toNat : v_pushed.toNat = tri_nat i.toNat :=
          UInt64.toNat_ofNat_of_lt' h_v_fits_odd
        have h_acc'_size : (push_one acc v_pushed h_acc_room).val.size = (i + 1).toNat := by
          rw [push_one_size, h_acc_size, h_i1_toNat]
        have h_acc'_inv :
            ∀ (j : Nat) (hj : j < (push_one acc v_pushed h_acc_room).val.size),
              ((push_one acc v_pushed h_acc_room).val[j]'hj).toNat = tri_nat j := by
          intro j hj
          by_cases hjlt : j < acc.val.size
          · rw [push_one_left acc v_pushed h_acc_room j hjlt hj]
            exact h_acc_inv j hjlt
          · have hj' : j < acc.val.size + 1 := by
              have := push_one_size acc v_pushed h_acc_room
              omega
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [push_one_back acc v_pushed h_acc_room hj]
            rw [h_acc_size]
            exact h_v_toNat
        rw [h_step]
        exact ih (i + 1) _ h_meas h_i1_le h_acc'_size h_acc'_inv

/-- Top-level: `tri n` fails when `n.toNat ≥ N_bound + 1`. -/
private theorem tri_fails_above_N (n : u64) (h_n_large : N_bound + 1 ≤ n.toNat) :
    ∀ v : alloc.vec.Vec u64 alloc.alloc.Global, clever_129_tri.tri n ≠ RustM.ok v := by
  intro v h_ok
  unfold clever_129_tri.tri at h_ok
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at h_ok
  -- Now h_ok : tri_at n 0 (empty_acc) = ok v
  let acc0 : alloc.vec.Vec u64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = (0 : u64).toNat := by
    show (List.nil : List u64).toArray.size = 0
    rfl
  have h_acc0_inv : ∀ (j : Nat) (hj : j < acc0.val.size),
      (acc0.val[j]'hj).toNat = tri_nat j := by
    intro j hj
    exfalso
    have h0 : acc0.val.size = 0 := by show (List.nil : List u64).toArray.size = 0; rfl
    rw [h0] at hj
    omega
  have h_i_le : (0 : u64).toNat ≤ N_bound + 1 := by rw [u64_zero_toNat]; omega
  have h_meas : N_bound + 1 - (0 : u64).toNat ≤ N_bound + 1 := by rw [u64_zero_toNat]; omega
  obtain ⟨e, h_fail⟩ := tri_at_fails n h_n_large (N_bound + 1) (0 : u64) acc0
                          h_meas h_i_le h_acc0_size h_acc0_inv
  rw [h_fail] at h_ok
  cases h_ok

/-! ## Top-level: `tri` aux. -/

private theorem tri_correct (n : u64) (hn : n.toNat ≤ N_bound) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_129_tri.tri n = RustM.ok v ∧
      v.val.size = n.toNat + 1 ∧
      (∀ (j : Nat) (hj : j < v.val.size), (v.val[j]'hj).toNat = tri_nat j) := by
  unfold clever_129_tri.tri
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind]
  let acc0 : alloc.vec.Vec u64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = (0 : u64).toNat := by
    show (List.nil : List u64).toArray.size = 0
    rfl
  have h_acc0_inv : ∀ (j : Nat) (hj : j < acc0.val.size),
      (acc0.val[j]'hj).toNat = tri_nat j := by
    intro j hj
    exfalso
    have h0 : acc0.val.size = 0 := by show (List.nil : List u64).toArray.size = 0; rfl
    rw [h0] at hj
    omega
  have h_i_le : (0 : u64).toNat ≤ n.toNat + 1 := by rw [u64_zero_toNat]; omega
  have h_meas : n.toNat + 1 - (0 : u64).toNat ≤ n.toNat + 1 := by rw [u64_zero_toNat]; omega
  exact tri_at_correct n hn (n.toNat + 1) (0 : u64) acc0 h_meas h_i_le h_acc0_size h_acc0_inv

/-! ## Public obligations from the Rust property tests. -/

/-- Postcondition 1 (length): the result has length `n + 1`. -/
theorem tri_length
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v) :
    v.val.size = n.toNat + 1 := by
  by_cases hn : n.toNat ≤ N_bound
  · obtain ⟨v', hres', hlen, _⟩ := tri_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact hlen
  · exfalso
    have hn' : N_bound + 1 ≤ n.toNat := by omega
    exact tri_fails_above_N n hn' v hres

/-- Postcondition 2a (base case at index 0): `r[0] = 3`. -/
theorem tri_index_zero
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (h0 : 0 < v.val.size) :
    (v.val[0]'h0).toNat = 3 := by
  by_cases hn : n.toNat ≤ N_bound
  · obtain ⟨v', hres', _, hinv⟩ := tri_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have := hinv 0 h0
    rw [this, tri_nat_zero]
  · exfalso
    have hn' : N_bound + 1 ≤ n.toNat := by omega
    exact tri_fails_above_N n hn' v hres

/-- Postcondition 2b (base case at index 1): `r[1] = 3` when `n ≥ 1`. -/
theorem tri_index_one
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (h1 : 1 < v.val.size) :
    (v.val[1]'h1).toNat = 3 := by
  by_cases hn : n.toNat ≤ N_bound
  · obtain ⟨v', hres', _, hinv⟩ := tri_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have := hinv 1 h1
    rw [this, tri_nat_one]
  · exfalso
    have hn' : N_bound + 1 ≤ n.toNat := by omega
    exact tri_fails_above_N n hn' v hres

/-- Postcondition 3 (even closed form): for even `i ≥ 2` in range,
    `r[i] = 1 + i / 2`. -/
theorem tri_even_closed_form
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (i : Nat) (h_ge : 2 ≤ i) (h_even : i % 2 = 0)
    (hi : i < v.val.size) :
    (v.val[i]'hi).toNat = 1 + i / 2 := by
  by_cases hn : n.toNat ≤ N_bound
  · obtain ⟨v', hres', _, hinv⟩ := tri_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have hat := hinv i hi
    rw [hat]
    exact tri_nat_even i h_ge h_even
  · exfalso
    have hn' : N_bound + 1 ≤ n.toNat := by omega
    exact tri_fails_above_N n hn' v hres

/-- Postcondition 4 (odd recurrence): for odd `i ≥ 3` with `i + 1` in range,
    `r[i] = r[i-1] + r[i-2] + r[i+1]`. -/
theorem tri_odd_recurrence
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (i : Nat) (h_ge : 3 ≤ i) (h_odd : i % 2 = 1)
    (hi_p1 : i + 1 < v.val.size)
    (hi_lt : i < v.val.size)
    (hi_m1 : i - 1 < v.val.size)
    (hi_m2 : i - 2 < v.val.size) :
    (v.val[i]'hi_lt).toNat =
      (v.val[i - 1]'hi_m1).toNat
      + (v.val[i - 2]'hi_m2).toNat
      + (v.val[i + 1]'hi_p1).toNat := by
  by_cases hn : n.toNat ≤ N_bound
  · obtain ⟨v', hres', _, hinv⟩ := tri_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have h_at := hinv i hi_lt
    have h_m1 := hinv (i - 1) hi_m1
    have h_m2 := hinv (i - 2) hi_m2
    have h_p1 := hinv (i + 1) hi_p1
    rw [h_at, h_m1, h_m2, h_p1]
    have h_iminus1_even : (i - 1) % 2 = 0 := by omega
    have h_iplus1_even : (i + 1) % 2 = 0 := by omega
    have h_iminus1_ge : 2 ≤ i - 1 := by omega
    have h_iplus1_ge : 2 ≤ i + 1 := by omega
    rw [tri_nat_even (i - 1) h_iminus1_ge h_iminus1_even]
    rw [tri_nat_even (i + 1) h_iplus1_ge h_iplus1_even]
    rw [tri_nat_odd i h_ge h_odd]
    omega
  · exfalso
    have hn' : N_bound + 1 ≤ n.toNat := by omega
    exact tri_fails_above_N n hn' v hres

end Clever_129_triObligations
