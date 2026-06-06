-- Companion obligations file for the `clever_099_make_a_pile` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_099_make_a_pile

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_099_make_a_pileObligations

/-! ## Helper lemmas (numeric / monadic bridges) -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide
private theorem usize_size_eq_2_64 : USize64.size = 2 ^ 64 := by decide

/-- `(d + 1).toNat = d.toNat + 1` when no overflow. -/
private theorem succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

/-- `2 *? k = pure (2 * k)` when no overflow. -/
private theorem mul_two_pure (k : u64) (h : 2 * k.toNat < 2 ^ 64) :
    ((2 : u64) *? k : RustM u64) = pure ((2 : u64) * k) := by
  show (rust_primitives.ops.arith.Mul.mul (2 : u64) k : RustM u64) = pure ((2 : u64) * k)
  show (if BitVec.umulOverflow (2 : u64).toBitVec k.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure ((2 : u64) * k)) = _
  have h_no : ¬ UInt64.mulOverflow (2 : u64) k := by
    rw [UInt64.mulOverflow_iff, u64_two_toNat]; omega
  have h_bv : BitVec.umulOverflow (2 : u64).toBitVec k.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

/-- `a +? b = pure (a + b)` when no overflow. -/
private theorem add_pure (a b : u64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b : RustM u64) = pure (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM u64) = pure (a + b)
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a + b)) = _
  have h_no : ¬ UInt64.addOverflow a b := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow a.toBitVec b.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `(2 * k).toNat = 2 * k.toNat` when no overflow. -/
private theorem mul_two_toNat (k : u64) (h : 2 * k.toNat < 2 ^ 64) :
    ((2 : u64) * k).toNat = 2 * k.toNat := by
  have h' : (2 : u64).toNat * k.toNat < 2 ^ 64 := by rw [u64_two_toNat]; exact h
  rw [UInt64.toNat_mul_of_lt h', u64_two_toNat]

/-- `(a + b).toNat = a.toNat + b.toNat` when no overflow. -/
private theorem add_toNat (a b : u64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := UInt64.toNat_add_of_lt h

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

@[simp]
private theorem push_one_size
    (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

/-! ## One-step reductions for `build_at` -/

/-- Out-of-bounds: `k ≥ n` → returns `acc`. -/
private theorem build_at_oob
    (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h : n.toNat ≤ k.toNat) :
    clever_099_make_a_pile.build_at n k acc = RustM.ok acc := by
  conv => lhs; unfold clever_099_make_a_pile.build_at
  have h_ge_u : k ≥ n := UInt64.le_iff_toNat_le.mpr h
  have h_dec : decide (k ≥ n) = true := decide_eq_true h_ge_u
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Push step: `k < n` and no overflows → push `n + 2*k`, recurse on `(k+1, acc++[n+2*k])`. -/
private theorem build_at_step
    (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat < n.toNat)
    (h_mul : 2 * k.toNat < 2 ^ 64)
    (h_add : n.toNat + 2 * k.toNat < 2 ^ 64)
    (h_inc : k.toNat + 1 < 2 ^ 64)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_099_make_a_pile.build_at n k acc =
      clever_099_make_a_pile.build_at n (k + 1)
        (push_one acc (n + (2 : u64) * k) h_acc) := by
  conv => lhs; unfold clever_099_make_a_pile.build_at
  have h_not_ge : ¬ k ≥ n := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    omega
  have h_dec_ge : decide (k ≥ n) = false := decide_eq_false h_not_ge
  -- 2 *? k = pure (2 * k)
  have h_mul_eq : ((2 : u64) *? k : RustM u64) = pure ((2 : u64) * k) :=
    mul_two_pure k h_mul
  -- (2 * k).toNat = 2 * k.toNat
  have h_2k_toNat : ((2 : u64) * k).toNat = 2 * k.toNat := mul_two_toNat k h_mul
  -- n +? (2 * k) = pure (n + 2 * k)
  have h_add_eq : (n +? ((2 : u64) * k) : RustM u64) = pure (n + (2 : u64) * k) := by
    apply add_pure
    rw [h_2k_toNat]; exact h_add
  -- k +? 1 = pure (k + 1)
  have h_inc_eq : (k +? (1 : u64) : RustM u64) = pure (k + 1) := by
    apply add_pure
    rw [u64_one_toNat]; exact h_inc
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec_ge, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [h_mul_eq]
  simp only [pure_bind]
  rw [h_add_eq]
  simp only [pure_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[n + (2 : u64) * k] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[n + (2 : u64) * k], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[n + (2 : u64) * k] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[n + (2 : u64) * k], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc (n + (2 : u64) * k) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_inc_eq]
  rfl

/-! ## Master induction over `build_at`. -/

private theorem build_at_correct
    (n : u64) (h_bound : 3 * n.toNat ≤ 2 ^ 64) :
    ∀ (m : Nat) (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      n.toNat - k.toNat ≤ m →
      k.toNat ≤ n.toNat →
      acc.val.size = k.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size),
          (acc.val[j]'hj).toNat = n.toNat + 2 * j) →
      ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
        clever_099_make_a_pile.build_at n k acc = RustM.ok v ∧
        v.val.size = n.toNat ∧
        ∀ (j : Nat) (hj : j < v.val.size),
          (v.val[j]'hj).toNat = n.toNat + 2 * j := by
  intro m
  induction m with
  | zero =>
    intro k acc hm hk_le h_size h_inv
    have hk_eq : k.toNat = n.toNat := by omega
    have hk_ge : n.toNat ≤ k.toNat := by omega
    refine ⟨acc, build_at_oob n k acc hk_ge, ?_, ?_⟩
    · rw [h_size, hk_eq]
    · intro j hj; exact h_inv j hj
  | succ m ih =>
    intro k acc hm hk_le h_size h_inv
    by_cases hk_ge : n.toNat ≤ k.toNat
    · have hk_eq : k.toNat = n.toNat := by omega
      refine ⟨acc, build_at_oob n k acc hk_ge, ?_, ?_⟩
      · rw [h_size, hk_eq]
      · intro j hj; exact h_inv j hj
    · have hk_lt : k.toNat < n.toNat := Nat.lt_of_not_le hk_ge
      -- Overflow witnesses from h_bound and k < n.
      have h_n_pos : 1 ≤ n.toNat := by omega
      have h_mul : 2 * k.toNat < 2 ^ 64 := by
        have h1 : 2 * k.toNat < 2 * n.toNat := by omega
        have h2 : 2 * n.toNat ≤ 3 * n.toNat := by omega
        omega
      have h_add : n.toNat + 2 * k.toNat < 2 ^ 64 := by
        have h1 : n.toNat + 2 * k.toNat ≤ 3 * n.toNat - 2 := by
          have h2 : k.toNat ≤ n.toNat - 1 := by omega
          have h3 : 2 * k.toNat ≤ 2 * (n.toNat - 1) := by omega
          omega
        omega
      have h_inc : k.toNat + 1 < 2 ^ 64 := by omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [usize_size_eq_2_64, h_size]; omega
      -- Step: rewrite build_at n k acc into build_at n (k+1) (push_one acc (n + 2*k) ...).
      rw [build_at_step n k acc hk_lt h_mul h_add h_inc h_acc_succ]
      -- toNat of the pushed element
      have h_2k_toNat : ((2 : u64) * k).toNat = 2 * k.toNat := mul_two_toNat k h_mul
      have h_n2k_toNat :
          (n + (2 : u64) * k).toNat = n.toNat + 2 * k.toNat := by
        have h_app := add_toNat n ((2 : u64) * k)
          (by rw [h_2k_toNat]; exact h_add)
        rw [h_app, h_2k_toNat]
      -- Successor toNat
      have h_succ_toNat : (k + 1).toNat = k.toNat + 1 := succ_toNat k h_inc
      -- Size invariant of the new acc
      have h_size' :
          (push_one acc (n + (2 : u64) * k) h_acc_succ).val.size = (k + 1).toNat := by
        rw [push_one_size, h_size, h_succ_toNat]
      -- Per-position invariant of the new acc
      have h_inv' :
          ∀ (j : Nat)
            (hj : j < (push_one acc (n + (2 : u64) * k) h_acc_succ).val.size),
            ((push_one acc (n + (2 : u64) * k) h_acc_succ).val[j]'hj).toNat =
              n.toNat + 2 * j := by
        intro j hj
        show ((acc.val ++ #[n + (2 : u64) * k])[j]'hj).toNat = n.toNat + 2 * j
        by_cases hj_lt : j < acc.val.size
        · rw [Array.getElem_append_left hj_lt]
          exact h_inv j hj_lt
        · have h_size_app :
              (acc.val ++ #[n + (2 : u64) * k]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have h_in : j < acc.val.size + 1 := by rw [← h_size_app]; exact hj
            omega
          subst hj_eq
          have h_ge : acc.val.size ≥ acc.val.size := Nat.le_refl _
          rw [Array.getElem_append_right h_ge]
          simp only [Nat.sub_self]
          show ((#[n + (2 : u64) * k] : Array u64)[0]).toNat = _
          rw [h_size]
          exact h_n2k_toNat
      have h_k1_le : (k + 1).toNat ≤ n.toNat := by rw [h_succ_toNat]; omega
      have h_meas : n.toNat - (k + 1).toNat ≤ m := by rw [h_succ_toNat]; omega
      exact ih (k + 1) (push_one acc (n + (2 : u64) * k) h_acc_succ)
        h_meas h_k1_le h_size' h_inv'

/-! ## Top-level wrapper: `make_a_pile`. -/

private theorem make_a_pile_aux
    (n : u64) (h_bound : 3 * n.toNat ≤ 2 ^ 64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_099_make_a_pile.make_a_pile n = RustM.ok v ∧
      v.val.size = n.toNat ∧
      ∀ (j : Nat) (hj : j < v.val.size),
        (v.val[j]'hj).toNat = n.toNat + 2 * j := by
  unfold clever_099_make_a_pile.make_a_pile
  have h_eq_def : ((n ==? (0 : u64)) : RustM Bool) = pure (n == (0 : u64)) := rfl
  simp only [h_eq_def, pure_bind]
  by_cases h_n_zero : n = (0 : u64)
  · -- n = 0 case
    have h_beq : (n == (0 : u64)) = true := by rw [h_n_zero]; rfl
    rw [h_beq]
    simp only [↓reduceIte]
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new]
    refine ⟨⟨(List.nil).toArray, by grind⟩, rfl, ?_, ?_⟩
    · show ((List.nil : List u64).toArray).size = n.toNat
      rw [h_n_zero]; rfl
    · intro j hj
      exfalso
      have h_size_zero :
          (⟨(List.nil : List u64).toArray, by grind⟩ :
             alloc.vec.Vec u64 alloc.alloc.Global).val.size = 0 := rfl
      rw [h_size_zero] at hj
      omega
  · -- n ≠ 0 case
    have h_beq : (n == (0 : u64)) = false := by
      show decide (n = (0 : u64)) = false
      exact decide_eq_false h_n_zero
    rw [h_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new]
    simp only [RustM_ok_bind]
    let acc0 : alloc.vec.Vec u64 alloc.alloc.Global :=
      ⟨(List.nil).toArray, by grind⟩
    have h_acc0_size : acc0.val.size = (0 : u64).toNat := by
      show ((List.nil : List u64).toArray).size = 0
      rfl
    have h_acc0_inv : ∀ (j : Nat) (hj : j < acc0.val.size),
        (acc0.val[j]'hj).toNat = n.toNat + 2 * j := by
      intro j hj
      exfalso
      have h0 : acc0.val.size = 0 := by
        show ((List.nil : List u64).toArray).size = 0; rfl
      rw [h0] at hj; omega
    have h_meas : n.toNat - (0 : u64).toNat ≤ n.toNat := by
      rw [u64_zero_toNat]; omega
    have h_le : (0 : u64).toNat ≤ n.toNat := by
      rw [u64_zero_toNat]; omega
    exact build_at_correct n h_bound n.toNat (0 : u64) acc0
      h_meas h_le h_acc0_size h_acc0_inv

/-!
The Rust source contains two contract-style property tests:

  * `length_is_n`       — postcondition (length): the returned `Vec`
                          has exactly `n` elements.
  * `element_formula`   — postcondition (contents): the element at
                          index `k` is `n + 2 * k` for every `k < n`.

Together these pin down the full specification of `make_a_pile`.

Note on the precondition. The proptest bounds `n ∈ [0, 1000)`, but the
Lean model permits any `u64`. For values of `n` near `u64::MAX`, the
inner recursion computes `2 *? k` for `k` up to `n − 1` (overflows if
`2 * (n − 1) ≥ 2^64`) and `n +? (2 * k)` whose worst case is
`n + 2 * (n − 1) = 3n − 2` (overflows if `3n − 2 ≥ 2^64`). The
strongest common precondition that prevents both overflows uniformly is
`3 * n.toNat ≤ USize64.size` (i.e. `≤ 2^64`):

  * for `n ≥ 1`, it yields `2 * (n − 1) ≤ 2 * n − 2 < 3n ≤ 2^64` and
    `3n − 2 < 2^64`;
  * for `n = 0`, the recursion is skipped entirely, so the bound is
    vacuously safe.

This is strictly weaker than the proptest's `n < 1000` and matches the
"safe arithmetic" idiom used by the existing references (e.g. the
`2 * s.val.size ≤ USize64.size` bound in `intersperse_modified`).
-/

/-- Length clause: the returned `Vec` has exactly `n` elements.
    Captures the Rust property test `length_is_n`. -/
theorem make_a_pile_length (n : u64) :
    ⦃ ⌜ 3 * n.toNat ≤ USize64.size ⌝ ⦄
    clever_099_make_a_pile.make_a_pile n
    ⦃ ⇓ r => ⌜ r.val.size = n.toNat ⌝ ⦄ := by
  intro hP
  have h_bound : 3 * n.toNat ≤ 2 ^ 64 := by rw [← usize_size_eq_2_64]; exact hP
  obtain ⟨v, hv_eq, hv_size, _⟩ := make_a_pile_aux n h_bound
  rw [hv_eq]
  exact hv_size

/-- Per-index formula: the element at position `k` equals `n + 2 * k`.
    Captures the Rust property test `element_formula`. -/
theorem make_a_pile_element_formula (n : u64) :
    ⦃ ⌜ 3 * n.toNat ≤ USize64.size ⌝ ⦄
    clever_099_make_a_pile.make_a_pile n
    ⦃ ⇓ r => ⌜ ∀ (k : Nat) (hk : k < r.val.size),
                  (r.val[k]'hk).toNat = n.toNat + 2 * k ⌝ ⦄ := by
  intro hP
  have h_bound : 3 * n.toNat ≤ 2 ^ 64 := by rw [← usize_size_eq_2_64]; exact hP
  obtain ⟨v, hv_eq, _, hv_inv⟩ := make_a_pile_aux n h_bound
  rw [hv_eq]
  intro k hk
  exact hv_inv k hk

end Clever_099_make_a_pileObligations
