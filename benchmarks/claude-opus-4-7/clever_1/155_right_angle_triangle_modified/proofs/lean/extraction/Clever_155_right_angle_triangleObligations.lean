-- Companion obligations file for the `clever_155_right_angle_triangle` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_155_right_angle_triangle

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_155_right_angle_triangleObligations

open clever_155_right_angle_triangle

/-! ## Numeric helper lemmas (u64 partial-operator discharge) -/

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl

/-- `x *? y = pure (x * y)` when `x.toNat * y.toNat` fits in `u64`. -/
private theorem mul_pure (x y : u64) (h : x.toNat * y.toNat < 2 ^ 64) :
    (x *? y : RustM u64) = pure (x * y) := by
  show (rust_primitives.ops.arith.Mul.mul x y : RustM u64) = pure (x * y)
  show (if BitVec.umulOverflow x.toBitVec y.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x * y)) = _
  have h_no : ¬ UInt64.mulOverflow x y := by
    rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow x.toBitVec y.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

/-- `x *? y = .fail .integerOverflow` when `x.toNat * y.toNat` does NOT fit. -/
private theorem mul_fail (x y : u64) (h : 2 ^ 64 ≤ x.toNat * y.toNat) :
    (x *? y : RustM u64) = .fail .integerOverflow := by
  show (rust_primitives.ops.arith.Mul.mul x y : RustM u64) = .fail .integerOverflow
  show (if BitVec.umulOverflow x.toBitVec y.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x * y)) = _
  have h_ov : UInt64.mulOverflow x y := by
    rw [UInt64.mulOverflow_iff]; exact h
  have h_bv : BitVec.umulOverflow x.toBitVec y.toBitVec = true := by
    simpa [UInt64.mulOverflow] using h_ov
  rw [h_bv]; rfl

/-- `x +? y = pure (x + y)` when `x.toNat + y.toNat` fits in `u64`. -/
private theorem add_pure (x y : u64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x +? y : RustM u64) = pure (x + y) := by
  show (rust_primitives.ops.arith.Add.add x y : RustM u64) = pure (x + y)
  show (if BitVec.uaddOverflow x.toBitVec y.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x + y)) = _
  have h_no : ¬ UInt64.addOverflow x y := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow x.toBitVec y.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- toNat after a multiplication that fits. -/
private theorem mul_toNat (x y : u64) (h : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := UInt64.toNat_mul_of_lt h

/-- toNat after an addition that fits. -/
private theorem add_toNat (x y : u64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := UInt64.toNat_add_of_lt h

private theorem u64_beq_decide_toNat (x y : u64) :
    (x == y) = decide (x.toNat = y.toNat) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    have hxy : x = y := by simpa using h
    rw [hxy]
  · intro h
    have hxy : x = y := UInt64.toNat_inj.mp h
    rw [hxy]; simp

private theorem aux_a2_lt {a b : u64}
    (h : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64) :
    a.toNat * a.toNat < 2 ^ 64 := by omega

private theorem aux_b2_lt {a b : u64}
    (h : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64) :
    b.toNat * b.toNat < 2 ^ 64 := by omega

/-- Reduce only as far as the first branch when its equality holds.
    Only `a*?a`, `b*?b`, `c*?c`, and `a*a +? b*b` need to succeed. -/
private theorem right_angle_triangle_first_branch (a b c : u64)
    (h_a2_fits : a.toNat * a.toNat < 2 ^ 64)
    (h_b2_fits : b.toNat * b.toNat < 2 ^ 64)
    (h_c2_fits : c.toNat * c.toNat < 2 ^ 64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (h_eq : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat) :
    right_angle_triangle a b c = RustM.ok true := by
  have h_a2 : (a *? a : RustM u64) = pure (a * a) := mul_pure a a h_a2_fits
  have h_b2 : (b *? b : RustM u64) = pure (b * b) := mul_pure b b h_b2_fits
  have h_c2 : (c *? c : RustM u64) = pure (c * c) := mul_pure c c h_c2_fits
  have h_a2_toNat : (a * a).toNat = a.toNat * a.toNat := mul_toNat a a h_a2_fits
  have h_b2_toNat : (b * b).toNat = b.toNat * b.toNat := mul_toNat b b h_b2_fits
  have h_c2_toNat : (c * c).toNat = c.toNat * c.toNat := mul_toNat c c h_c2_fits
  have hab' : (a * a).toNat + (b * b).toNat < 2 ^ 64 := by
    rw [h_a2_toNat, h_b2_toNat]; exact hab
  have h_ab_sum : ((a * a) +? (b * b) : RustM u64) = pure ((a * a) + (b * b)) :=
    add_pure (a * a) (b * b) hab'
  have h_ab_toNat : (a * a + b * b).toNat = a.toNat * a.toNat + b.toNat * b.toNat := by
    rw [add_toNat _ _ hab', h_a2_toNat, h_b2_toNat]
  have h_eq_u64 : (a * a + b * b) = c * c := by
    apply UInt64.toNat_inj.mp
    rw [h_ab_toNat, h_c2_toNat]; exact h_eq
  have eq_unfold : ∀ (x y : u64), (x ==? y : RustM Bool) = pure (x == y) := by intros; rfl
  unfold right_angle_triangle
  rw [h_a2, h_b2, h_c2]
  simp only [pure_bind]
  rw [h_ab_sum]
  simp only [pure_bind, eq_unfold]
  rw [h_eq_u64]
  simp only [pure_bind, BEq.refl, if_true]
  rfl

/-- Reduce when the first branch fails and the second branch holds. -/
private theorem right_angle_triangle_second_branch (a b c : u64)
    (h_a2_fits : a.toNat * a.toNat < 2 ^ 64)
    (h_b2_fits : b.toNat * b.toNat < 2 ^ 64)
    (h_c2_fits : c.toNat * c.toNat < 2 ^ 64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (hac : a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64)
    (h_neq : ¬ a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat)
    (h_eq : a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat) :
    right_angle_triangle a b c = RustM.ok true := by
  have h_a2 : (a *? a : RustM u64) = pure (a * a) := mul_pure a a h_a2_fits
  have h_b2 : (b *? b : RustM u64) = pure (b * b) := mul_pure b b h_b2_fits
  have h_c2 : (c *? c : RustM u64) = pure (c * c) := mul_pure c c h_c2_fits
  have h_a2_toNat : (a * a).toNat = a.toNat * a.toNat := mul_toNat a a h_a2_fits
  have h_b2_toNat : (b * b).toNat = b.toNat * b.toNat := mul_toNat b b h_b2_fits
  have h_c2_toNat : (c * c).toNat = c.toNat * c.toNat := mul_toNat c c h_c2_fits
  have hab' : (a * a).toNat + (b * b).toNat < 2 ^ 64 := by
    rw [h_a2_toNat, h_b2_toNat]; exact hab
  have hac' : (a * a).toNat + (c * c).toNat < 2 ^ 64 := by
    rw [h_a2_toNat, h_c2_toNat]; exact hac
  have h_ab_sum : ((a * a) +? (b * b) : RustM u64) = pure ((a * a) + (b * b)) :=
    add_pure (a * a) (b * b) hab'
  have h_ac_sum : ((a * a) +? (c * c) : RustM u64) = pure ((a * a) + (c * c)) :=
    add_pure (a * a) (c * c) hac'
  have h_ab_toNat : (a * a + b * b).toNat = a.toNat * a.toNat + b.toNat * b.toNat := by
    rw [add_toNat _ _ hab', h_a2_toNat, h_b2_toNat]
  have h_ac_toNat : (a * a + c * c).toNat = a.toNat * a.toNat + c.toNat * c.toNat := by
    rw [add_toNat _ _ hac', h_a2_toNat, h_c2_toNat]
  have h_neq_u64 : (a * a + b * b) ≠ c * c := by
    intro h_eq2
    have h_nat : (a * a + b * b).toNat = (c * c).toNat := by rw [h_eq2]
    rw [h_ab_toNat, h_c2_toNat] at h_nat
    exact h_neq h_nat
  have h_eq_u64 : (a * a + c * c) = b * b := by
    apply UInt64.toNat_inj.mp
    rw [h_ac_toNat, h_b2_toNat]; exact h_eq
  have eq_unfold : ∀ (x y : u64), (x ==? y : RustM Bool) = pure (x == y) := by intros; rfl
  have h_e1_false : ((a*a + b*b) == c*c) = false := by
    rw [Bool.eq_false_iff]; intro h
    have : (a*a + b*b) = c*c := by simpa using h
    exact h_neq_u64 this
  unfold right_angle_triangle
  rw [h_a2, h_b2, h_c2]
  simp only [pure_bind]
  rw [h_ab_sum]
  simp only [pure_bind, eq_unfold]
  rw [h_e1_false]
  simp only [Bool.false_eq_true, if_false]
  rw [h_ac_sum]
  simp only [pure_bind, eq_unfold]
  rw [h_eq_u64]
  simp only [pure_bind, BEq.refl, if_true]
  rfl

/-- Master reduction: under no-overflow on every pairwise sum,
    `right_angle_triangle` returns an `ok` with an explicit Boolean cascade. -/
private theorem right_angle_triangle_reduce (a b c : u64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (hac : a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64)
    (hbc : b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64) :
    right_angle_triangle a b c = RustM.ok
      (if a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat then true
       else if a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat then true
       else decide (b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat)) := by
  have h_a2_fits : a.toNat * a.toNat < 2 ^ 64 := aux_a2_lt hab
  have h_b2_fits : b.toNat * b.toNat < 2 ^ 64 := aux_b2_lt hab
  have h_c2_fits : c.toNat * c.toNat < 2 ^ 64 := aux_b2_lt hac
  have h_a2 : (a *? a : RustM u64) = pure (a * a) := mul_pure a a h_a2_fits
  have h_b2 : (b *? b : RustM u64) = pure (b * b) := mul_pure b b h_b2_fits
  have h_c2 : (c *? c : RustM u64) = pure (c * c) := mul_pure c c h_c2_fits
  have h_a2_toNat : (a * a).toNat = a.toNat * a.toNat := mul_toNat a a h_a2_fits
  have h_b2_toNat : (b * b).toNat = b.toNat * b.toNat := mul_toNat b b h_b2_fits
  have h_c2_toNat : (c * c).toNat = c.toNat * c.toNat := mul_toNat c c h_c2_fits
  have hab' : (a * a).toNat + (b * b).toNat < 2 ^ 64 := by
    rw [h_a2_toNat, h_b2_toNat]; exact hab
  have hac' : (a * a).toNat + (c * c).toNat < 2 ^ 64 := by
    rw [h_a2_toNat, h_c2_toNat]; exact hac
  have hbc' : (b * b).toNat + (c * c).toNat < 2 ^ 64 := by
    rw [h_b2_toNat, h_c2_toNat]; exact hbc
  have h_ab_sum : ((a * a) +? (b * b) : RustM u64) = pure ((a * a) + (b * b)) :=
    add_pure (a * a) (b * b) hab'
  have h_ac_sum : ((a * a) +? (c * c) : RustM u64) = pure ((a * a) + (c * c)) :=
    add_pure (a * a) (c * c) hac'
  have h_bc_sum : ((b * b) +? (c * c) : RustM u64) = pure ((b * b) + (c * c)) :=
    add_pure (b * b) (c * c) hbc'
  have h_ab_toNat : (a * a + b * b).toNat = a.toNat * a.toNat + b.toNat * b.toNat := by
    rw [add_toNat _ _ hab', h_a2_toNat, h_b2_toNat]
  have h_ac_toNat : (a * a + c * c).toNat = a.toNat * a.toNat + c.toNat * c.toNat := by
    rw [add_toNat _ _ hac', h_a2_toNat, h_c2_toNat]
  have h_bc_toNat : (b * b + c * c).toNat = b.toNat * b.toNat + c.toNat * c.toNat := by
    rw [add_toNat _ _ hbc', h_b2_toNat, h_c2_toNat]
  -- Equalities translating u64-BEq to Nat-equality `decide` on the relevant sums.
  have h_e1 : ((a*a + b*b) == c*c) =
      decide (a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat) := by
    rw [u64_beq_decide_toNat, h_ab_toNat, h_c2_toNat]
  have h_e2 : ((a*a + c*c) == b*b) =
      decide (a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat) := by
    rw [u64_beq_decide_toNat, h_ac_toNat, h_b2_toNat]
  have h_e3 : ((b*b + c*c) == a*a) =
      decide (b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat) := by
    rw [u64_beq_decide_toNat, h_bc_toNat, h_a2_toNat]
  -- Helper unfolds for ==? operator.
  have eq_unfold : ∀ (x y : u64), (x ==? y : RustM Bool) = pure (x == y) := by
    intros; rfl
  unfold right_angle_triangle
  rw [h_a2, h_b2, h_c2]
  simp only [pure_bind]
  rw [h_ab_sum]
  simp only [pure_bind, eq_unfold, h_e1]
  by_cases h1 : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat
  · rw [decide_eq_true h1]; simp only [if_true]; rw [if_pos h1]; rfl
  · rw [decide_eq_false h1]
    simp only [Bool.false_eq_true, if_false]
    rw [h_ac_sum]
    simp only [pure_bind, eq_unfold, h_e2]
    rw [if_neg h1]
    by_cases h2 : a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat
    · rw [decide_eq_true h2]; simp only [if_true]; rw [if_pos h2]; rfl
    · rw [decide_eq_false h2]
      simp only [Bool.false_eq_true, if_false]
      rw [if_neg h2]
      rw [h_bc_sum]
      simp only [pure_bind, eq_unfold, h_e3]
      rfl

/-! ## Failure mode -/

theorem right_angle_triangle_overflow_a (a b c : u64)
    (h : 2 ^ 64 ≤ a.toNat * a.toNat) :
    right_angle_triangle a b c = RustM.fail Error.integerOverflow := by
  have h_fail : (a *? a : RustM u64) = .fail .integerOverflow := mul_fail a a h
  unfold right_angle_triangle
  rw [h_fail]
  rfl

/-! ## Functional correctness (docstring spec) -/

theorem right_angle_triangle_spec (a b c : u64) :
    ⦃ ⌜ a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64 ∧
        a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64 ∧
        b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64 ⌝ ⦄
    right_angle_triangle a b c
    ⦃ ⇓ r => ⌜ r = true ↔
        a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat ∨
        a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat ∨
        b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat ⌝ ⦄ := by
  rw [RustM.Triple_iff_BitVec]
  rw [Bool.or_eq_true, Bool.and_eq_true]
  -- Goal: !decide pre = true ∨ (... .ok = true ∧ decide post = true)
  -- Right disjunct: show pre → ok ∧ post.
  by_cases h_pre :
      a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64 ∧
      a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64 ∧
      b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64
  · right
    obtain ⟨hab, hac, hbc⟩ := h_pre
    rw [right_angle_triangle_reduce a b c hab hac hbc]
    refine ⟨rfl, ?_⟩
    apply decide_eq_true
    -- Show: (if … then true else …) = true ↔ disjunction
    by_cases h1 : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat
    · rw [if_pos h1]
      exact ⟨fun _ => Or.inl h1, fun _ => rfl⟩
    · rw [if_neg h1]
      by_cases h2 : a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat
      · rw [if_pos h2]
        exact ⟨fun _ => Or.inr (Or.inl h2), fun _ => rfl⟩
      · rw [if_neg h2]
        constructor
        · intro h
          have h3 : b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat :=
            of_decide_eq_true h
          exact Or.inr (Or.inr h3)
        · intro h
          rcases h with h | h | h
          · exact absurd h h1
          · exact absurd h h2
          · exact decide_eq_true h
  · left; simp [h_pre]

/-! ## Permutation invariance -/

theorem right_angle_triangle_swap_ab (a b c : u64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (hac : a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64)
    (hbc : b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64) :
    right_angle_triangle a b c = right_angle_triangle b a c := by
  have hba : b.toNat * b.toNat + a.toNat * a.toNat < 2 ^ 64 := by omega
  rw [right_angle_triangle_reduce a b c hab hac hbc,
      right_angle_triangle_reduce b a c hba hbc hac]
  congr 1
  -- Goal: cascade(a,b,c) = cascade(b,a,c)
  -- LHS: if a²+b²=c² then T else if a²+c²=b² then T else dec(b²+c²=a²)
  -- RHS: if b²+a²=c² then T else if b²+c²=a² then T else dec(a²+c²=b²)
  -- First guards are equal by commutativity of +.
  by_cases h1 : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat
  · have h1' : b.toNat * b.toNat + a.toNat * a.toNat = c.toNat * c.toNat := by omega
    rw [if_pos h1, if_pos h1']
  · have h1' : ¬ b.toNat * b.toNat + a.toNat * a.toNat = c.toNat * c.toNat := by omega
    rw [if_neg h1, if_neg h1']
    -- LHS now: if a²+c²=b² then T else dec(b²+c²=a²)
    -- RHS now: if b²+c²=a² then T else dec(a²+c²=b²)
    -- Both branches share the pair (a²+c²=b², b²+c²=a²) but in swapped order.
    by_cases h2 : a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat
    · rw [if_pos h2]
      by_cases h3 : b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat
      · rw [if_pos h3]
      · rw [if_neg h3]
        rw [decide_eq_true h2]
    · rw [if_neg h2]
      by_cases h3 : b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat
      · rw [if_pos h3]
        rw [decide_eq_true h3]
      · rw [if_neg h3]
        rw [decide_eq_false h2, decide_eq_false h3]

theorem right_angle_triangle_swap_bc (a b c : u64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (hac : a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64)
    (hbc : b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64) :
    right_angle_triangle a b c = right_angle_triangle a c b := by
  have hcb : c.toNat * c.toNat + b.toNat * b.toNat < 2 ^ 64 := by omega
  rw [right_angle_triangle_reduce a b c hab hac hbc,
      right_angle_triangle_reduce a c b hac hab hcb]
  congr 1
  -- LHS: if a²+b²=c² then T else if a²+c²=b² then T else dec(b²+c²=a²)
  -- RHS: if a²+c²=b² then T else if a²+b²=c² then T else dec(c²+b²=a²)
  by_cases h1 : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat
  · -- LHS = T. RHS: first guard is `a²+c²=b²`.
    rw [if_pos h1]
    by_cases h2 : a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat
    · -- LHS = T. RHS first guard is true.
      rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h1]
      -- Both decide goals: LHS dec(b²+c²=a²), RHS dec(c²+b²=a²).
      have h_comm : b.toNat * b.toNat + c.toNat * c.toNat
                  = c.toNat * c.toNat + b.toNat * b.toNat := by omega
      by_cases h3 : b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat
      · have h3' : c.toNat * c.toNat + b.toNat * b.toNat = a.toNat * a.toNat := by omega
        rw [decide_eq_true h3, decide_eq_true h3']
      · have h3' : ¬ c.toNat * c.toNat + b.toNat * b.toNat = a.toNat * a.toNat := by omega
        rw [decide_eq_false h3, decide_eq_false h3']

/-! ## Pythagorean recognition (positive direction) -/

theorem right_angle_triangle_recognises_pythagorean (a b c : u64)
    (h_a2 : a.toNat * a.toNat < 2 ^ 64)
    (h_b2 : b.toNat * b.toNat < 2 ^ 64)
    (h_ab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (h_pyth : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat) :
    right_angle_triangle a b c = RustM.ok true := by
  -- The Pythagorean equality forces `c² < 2^64` for free.
  have h_c2 : c.toNat * c.toNat < 2 ^ 64 := by rw [← h_pyth]; exact h_ab
  exact right_angle_triangle_first_branch a b c h_a2 h_b2 h_c2 h_ab h_pyth

/-! ## Equilateral (negative direction) -/

theorem right_angle_triangle_equilateral_positive_not_right (a : u64)
    (h_pos : 0 < a.toNat)
    (h_fits : 2 * (a.toNat * a.toNat) < 2 ^ 64) :
    right_angle_triangle a a a = RustM.ok false := by
  have h_sum_fits : a.toNat * a.toNat + a.toNat * a.toNat < 2 ^ 64 := by omega
  rw [right_angle_triangle_reduce a a a h_sum_fits h_sum_fits h_sum_fits]
  congr 1
  -- All three "if" guards `2a² = a²` are false because `a > 0`.
  have h_a2_pos : 0 < a.toNat * a.toNat := Nat.mul_pos h_pos h_pos
  have h_neq : ¬ a.toNat * a.toNat + a.toNat * a.toNat = a.toNat * a.toNat := by omega
  rw [if_neg h_neq, if_neg h_neq]
  exact decide_eq_false h_neq

/-! ## Zero-side boundary cases -/

theorem right_angle_triangle_zero_first (n : u64)
    (h_fits : n.toNat * n.toNat < 2 ^ 64) :
    right_angle_triangle 0 n n = RustM.ok true := by
  apply right_angle_triangle_first_branch
  · show (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64; rw [u64_zero_toNat]; decide
  · exact h_fits
  · exact h_fits
  · show (0 : u64).toNat * (0 : u64).toNat + n.toNat * n.toNat < 2 ^ 64
    rw [u64_zero_toNat]; simp; exact h_fits
  · show (0 : u64).toNat * (0 : u64).toNat + n.toNat * n.toNat = n.toNat * n.toNat
    rw [u64_zero_toNat]; simp

theorem right_angle_triangle_zero_middle (n : u64)
    (h_fits : n.toNat * n.toNat < 2 ^ 64) :
    right_angle_triangle n 0 n = RustM.ok true := by
  apply right_angle_triangle_first_branch
  · exact h_fits
  · show (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64; rw [u64_zero_toNat]; decide
  · exact h_fits
  · show n.toNat * n.toNat + (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64
    rw [u64_zero_toNat]; simp; exact h_fits
  · show n.toNat * n.toNat + (0 : u64).toNat * (0 : u64).toNat = n.toNat * n.toNat
    rw [u64_zero_toNat]; simp

theorem right_angle_triangle_zero_last (n : u64)
    (h_fits : 2 * (n.toNat * n.toNat) < 2 ^ 64) :
    right_angle_triangle n n 0 = RustM.ok true := by
  have h_n2_fits : n.toNat * n.toNat < 2 ^ 64 := by omega
  have h_0_fits : (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64 := by
    rw [u64_zero_toNat]; decide
  have h_ab_fits : n.toNat * n.toNat + n.toNat * n.toNat < 2 ^ 64 := by omega
  have h_ac_fits : n.toNat * n.toNat + (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64 := by
    rw [u64_zero_toNat]; simp; exact h_n2_fits
  by_cases h_n_zero : n.toNat = 0
  · -- n = 0: all three sides zero, first branch is trivially true.
    have h_n_eq_zero : n = 0 := by
      apply UInt64.toNat_inj.mp; rw [h_n_zero, u64_zero_toNat]
    rw [h_n_eq_zero]
    apply right_angle_triangle_first_branch
    · exact h_0_fits
    · exact h_0_fits
    · exact h_0_fits
    · show (0 : u64).toNat * (0 : u64).toNat + (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64
      rw [u64_zero_toNat]; decide
    · show (0 : u64).toNat * (0 : u64).toNat + (0 : u64).toNat * (0 : u64).toNat = (0 : u64).toNat * (0 : u64).toNat
      rw [u64_zero_toNat]
  · -- n > 0: first branch is `n² + n² == 0` which is false, second is `n² + 0 == n²` which is true.
    have h_n_pos : 0 < n.toNat := Nat.pos_of_ne_zero h_n_zero
    apply right_angle_triangle_second_branch
    · exact h_n2_fits
    · exact h_n2_fits
    · exact h_0_fits
    · exact h_ab_fits
    · exact h_ac_fits
    · -- ¬ (n² + n² = 0² = 0)
      show ¬ n.toNat * n.toNat + n.toNat * n.toNat = (0 : u64).toNat * (0 : u64).toNat
      rw [u64_zero_toNat]
      have h_n2_pos : 0 < n.toNat * n.toNat := Nat.mul_pos h_n_pos h_n_pos
      omega
    · -- n² + 0 = n²
      show n.toNat * n.toNat + (0 : u64).toNat * (0 : u64).toNat = n.toNat * n.toNat
      rw [u64_zero_toNat]; simp

end Clever_155_right_angle_triangleObligations
