-- Companion obligations file for the `cbrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import cbrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Cbrt_u64Obligations

/-! ## Helper lemmas for the cube-root proof.

These mirror the algebraic identities used in `sqrt_u64_modified` but
adapted for the cubic Newton recurrence `(a/x² + 2x)/3` and the
Hacker's-Delight `icbrt2` invariant `y³ · 8^s_iter ≤ a < (y+1)³ · 8^s_iter`. -/

@[simp] private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- Polynomial identity for `(a + b)²`. -/
private theorem nat_sq_expand (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  have h1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) := Nat.add_mul a b (a + b)
  have h2 : a * (a + b) = a * a + a * b := Nat.mul_add a a b
  have h3 : b * (a + b) = b * a + b * b := Nat.mul_add b a b
  have h4 : b * a = a * b := Nat.mul_comm b a
  omega

/-- 2-variable AM-GM: `q² + x² ≥ 2qx`. -/
private theorem nat_sq_sum_ge_2_mul (q x : Nat) : 2*(q*x) ≤ q*q + x*x := by
  by_cases h : q ≥ x
  · obtain ⟨d, rfl⟩ : ∃ d, q = x + d := ⟨q - x, by omega⟩
    have h_sq := nat_sq_expand x d
    have h_mul : (x+d)*x = x*x + d*x := by rw [Nat.add_mul]
    rw [h_mul, h_sq]
    have h_dx_xd : d*x = x*d := Nat.mul_comm d x
    omega
  · obtain ⟨d, rfl⟩ : ∃ d, x = q + d := ⟨x - q, by omega⟩
    have h_sq := nat_sq_expand q d
    have h_mul : q*(q+d) = q*q + q*d := by rw [Nat.mul_add]
    rw [h_mul, h_sq]
    omega

/-- Binomial cube expansion: `(a+b)³ = a³ + 3a²b + 3ab² + b³`. -/
private theorem nat_cube_expand (a b : Nat) :
    (a + b) * (a + b) * (a + b) = a*a*a + 3*(a*a*b) + 3*(a*b*b) + b*b*b := by
  have h_sq : (a + b) * (a + b) = a*a + 2*(a*b) + b*b := nat_sq_expand a b
  show (a + b) * (a + b) * (a + b) = _
  rw [h_sq, Nat.add_mul, Nat.add_mul,
      Nat.mul_add (a*a) a b, Nat.mul_add (2*(a*b)) a b, Nat.mul_add (b*b) a b]
  -- Normalise product terms via comm/assoc.
  have h1 : 2*(a*b)*a = 2*(a*a*b) := by
    have h_swap : (a*b)*a = a*a*b := by
      rw [Nat.mul_assoc a b a, Nat.mul_comm b a, ← Nat.mul_assoc]
    rw [Nat.mul_assoc 2 (a*b) a, h_swap]
  have h2 : 2*(a*b)*b = 2*(a*b*b) := Nat.mul_assoc 2 (a*b) b
  have h3 : b*b*a = a*b*b := by
    rw [Nat.mul_comm (b*b) a, ← Nat.mul_assoc]
  rw [h1, h2, h3]
  omega

/-- Cubic AM-GM (3-variable, two equal): `(q + 2x)³ ≥ 27qx²`. The
    mathematical core of the cubic Newton step lemma. -/
private theorem nat_cubic_amgm (q x : Nat) :
    27 * (q * x * x) ≤ (q + 2*x) * (q + 2*x) * (q + 2*x) := by
  -- Cube expansion: (q+2x)³ = q³ + 6 q²x + 12 q x² + 8 x³.
  have h_cube : (q + 2*x) * (q + 2*x) * (q + 2*x) =
      q*q*q + 6*(q*q*x) + 12*(q*x*x) + 8*(x*x*x) := by
    rw [nat_cube_expand q (2*x)]
    have e1 : q*q*(2*x) = 2*(q*q*x) := by
      rw [← Nat.mul_assoc (q*q) 2 x, Nat.mul_comm (q*q) 2, Nat.mul_assoc]
    have e2 : q*(2*x)*(2*x) = 4*(q*x*x) := by
      have step1 : q*(2*x) = 2*(q*x) := by
        rw [← Nat.mul_assoc q 2 x, Nat.mul_comm q 2, Nat.mul_assoc]
      rw [step1, Nat.mul_assoc 2 (q*x) (2*x)]
      have step2 : (q*x)*(2*x) = 2*((q*x)*x) := by
        rw [← Nat.mul_assoc (q*x) 2 x, Nat.mul_comm (q*x) 2, Nat.mul_assoc]
      rw [step2, ← Nat.mul_assoc]
    have e3 : (2*x)*(2*x)*(2*x) = 8*(x*x*x) := by
      have step1 : (2*x)*(2*x) = 4*(x*x) := by
        rw [← Nat.mul_assoc (2*x) 2 x, Nat.mul_comm (2*x) 2, Nat.mul_assoc]
        -- Goal: 2 * (2 * x * x) = 4 * (x * x)
        rw [show (2*x*x : Nat) = 2*(x*x) from Nat.mul_assoc 2 x x]
        rw [← Nat.mul_assoc 2 2 (x*x)]
      rw [step1, Nat.mul_assoc 4 (x*x) (2*x)]
      have step2 : (x*x)*(2*x) = 2*((x*x)*x) := by
        rw [← Nat.mul_assoc (x*x) 2 x, Nat.mul_comm (x*x) 2, Nat.mul_assoc]
      rw [step2, ← Nat.mul_assoc]
    rw [e1, e2, e3]
    omega
  -- Two AM-GM-derived inequalities:
  --   (a) 2 * q²x ≤ q³ + q x²   (from q²+x² ≥ 2qx, multiplied by q)
  --   (b) 2 * q x² ≤ q²x + x³   (from q²+x² ≥ 2qx, multiplied by x)
  have h_amgm := nat_sq_sum_ge_2_mul q x  -- 2*(q*x) ≤ q*q + x*x
  have h_a : 2*(q*q*x) ≤ q*q*q + q*x*x := by
    have h := Nat.mul_le_mul_right q h_amgm
    have e_lhs : 2*(q*x) * q = 2*(q*q*x) := by
      rw [Nat.mul_assoc 2 (q*x) q, Nat.mul_comm (q*x) q, ← Nat.mul_assoc q q x]
    have e_rhs : (q*q + x*x) * q = q*q*q + q*x*x := by
      rw [Nat.add_mul]
      have h_xxq : x*x*q = q*x*x := by
        rw [Nat.mul_comm (x*x) q, ← Nat.mul_assoc]
      rw [h_xxq]
    rw [e_lhs, e_rhs] at h
    exact h
  have h_b : 2*(q*x*x) ≤ q*q*x + x*x*x := by
    have h := Nat.mul_le_mul_right x h_amgm
    have e_lhs : 2*(q*x) * x = 2*(q*x*x) := by
      rw [Nat.mul_assoc 2 (q*x) x]
    have e_rhs : (q*q + x*x) * x = q*q*x + x*x*x := by
      rw [Nat.add_mul]
    rw [e_lhs, e_rhs] at h
    exact h
  -- Combine using omega: with h_a, h_b, and h_cube.
  rw [h_cube]
  omega

/-- `(3·n)³ = 27·n³`. Helper for the Newton lower-bound lemma. -/
private theorem nat_three_mul_cube (n : Nat) :
    (3*n) * (3*n) * (3*n) = 27 * (n*n*n) := by
  have h1 : 3*n*(3*n) = 9*(n*n) := by
    rw [Nat.mul_assoc 3 n (3*n)]
    have h_in : n * (3*n) = 3 * (n*n) := by
      rw [← Nat.mul_assoc n 3 n, Nat.mul_comm n 3, Nat.mul_assoc]
    rw [h_in, ← Nat.mul_assoc]
  rw [h1, Nat.mul_assoc 9 (n*n) (3*n)]
  have h2 : n*n*(3*n) = 3*(n*n*n) := by
    rw [← Nat.mul_assoc (n*n) 3 n, Nat.mul_comm (n*n) 3, Nat.mul_assoc]
  rw [h2, ← Nat.mul_assoc]

/-- Newton step lower bound: for `0 < x`, the cubic Newton iterate
    `f = (a/x² + 2x)/3` satisfies `a < (f + 1)³`. -/
private theorem nat_cubic_newton_lb (a x : Nat) (hx : 0 < x) :
    a < ((a / (x*x) + 2*x) / 3 + 1) * ((a / (x*x) + 2*x) / 3 + 1)
          * ((a / (x*x) + 2*x) / 3 + 1) := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  -- (P1) q*(x*x) ≤ a < (q+1)*(x*x), where q = a/(x*x).
  have h_q_lb : a / (x*x) * (x*x) ≤ a := Nat.div_mul_le_self a (x*x)
  have h_q_ub : a < (a / (x*x) + 1) * (x*x) := by
    have h_div_mod := Nat.div_add_mod a (x*x)
    have h_mod_lt : a % (x*x) < x*x := Nat.mod_lt a hxx_pos
    have h_comm : (x*x) * (a / (x*x)) = a / (x*x) * (x*x) := Nat.mul_comm _ _
    have h_factor : a / (x*x) * (x*x) + x*x = (a / (x*x) + 1) * (x*x) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  -- (P2) 3*(f+1) ≥ q + 2x + 1.
  have h_3f : 3 * ((a / (x*x) + 2*x) / 3 + 1) ≥ a / (x*x) + 2*x + 1 := by
    have h_div_mod := Nat.div_add_mod (a / (x*x) + 2*x) 3
    have h_mod_lt : (a / (x*x) + 2*x) % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  -- (P3) Cubic AM-GM at (q+1, x): ((q+1) + 2x)³ ≥ 27 * (q+1) * x * x.
  have h_amgm := nat_cubic_amgm (a / (x*x) + 1) x
  -- (P4) (q+1) * x * x = (q+1) * (x*x).
  have h_q1xx : (a / (x*x) + 1) * x * x = (a / (x*x) + 1) * (x*x) := by
    rw [Nat.mul_assoc]
  -- (P5) (q+1)*(x*x) ≥ a + 1 (from P1).
  have h_q1xx_ge : (a / (x*x) + 1) * (x*x) ≥ a + 1 := by
    have h := h_q_ub; omega
  -- (P6) (q+1+2x)³ ≥ 27*(a+1) = 27a + 27.
  have h_q1_cube : (a / (x*x) + 1 + 2*x) * (a / (x*x) + 1 + 2*x)
                     * (a / (x*x) + 1 + 2*x) ≥ 27 * a + 27 := by
    have h := h_amgm
    rw [h_q1xx] at h
    have h_mul_27 : 27 * ((a / (x*x) + 1) * (x*x)) ≥ 27 * (a + 1) := by
      exact Nat.mul_le_mul_left 27 h_q1xx_ge
    omega
  -- (P7) Cube both sides of h_3f: (3*(f+1))³ ≥ (q+1+2x)³ ≥ 27a+27.
  have h_rearrange : a / (x*x) + 2*x + 1 = a / (x*x) + 1 + 2*x := by omega
  rw [h_rearrange] at h_3f
  have h_cube_ge : (3 * ((a / (x*x) + 2*x) / 3 + 1))
                     * (3 * ((a / (x*x) + 2*x) / 3 + 1))
                     * (3 * ((a / (x*x) + 2*x) / 3 + 1))
                   ≥ (a / (x*x) + 1 + 2*x) * (a / (x*x) + 1 + 2*x)
                       * (a / (x*x) + 1 + 2*x) :=
    Nat.mul_le_mul (Nat.mul_le_mul h_3f h_3f) h_3f
  -- (P8) (3*(f+1))³ = 27 * (f+1)³.
  have h_27_cube := nat_three_mul_cube ((a / (x*x) + 2*x) / 3 + 1)
  -- Combine: 27 * (f+1)³ ≥ 27a + 27.
  have h_27_f1 : 27 * (((a / (x*x) + 2*x) / 3 + 1) * ((a / (x*x) + 2*x) / 3 + 1)
                     * ((a / (x*x) + 2*x) / 3 + 1)) ≥ 27 * a + 27 := by
    rw [← h_27_cube]
    omega
  -- Divide by 27 (omega handles 27 * N ≥ 27 * (a+1) → N ≥ a + 1).
  omega

/-- Loop-up exit lemma: if `(a/x² + 2x)/3 ≤ x` then `a < (x+1)³`. -/
private theorem nat_iter_cbrt_le_self_implies (a x : Nat) (hx : 0 < x)
    (h_le : (a / (x*x) + 2*x) / 3 ≤ x) :
    a < (x + 1) * (x + 1) * (x + 1) := by
  have h_lb := nat_cubic_newton_lb a x hx
  -- ((a/x²+2x)/3 + 1)³ ≤ (x+1)³ since (a/x²+2x)/3 ≤ x.
  have h_sq_le : ((a / (x*x) + 2*x) / 3 + 1) * ((a / (x*x) + 2*x) / 3 + 1)
                  * ((a / (x*x) + 2*x) / 3 + 1)
                ≤ (x + 1) * (x + 1) * (x + 1) := by
    have h_step : (a / (x*x) + 2*x) / 3 + 1 ≤ x + 1 :=
      Nat.add_le_add_right h_le 1
    exact Nat.mul_le_mul (Nat.mul_le_mul h_step h_step) h_step
  omega

/-- Loop-down exit characterisation: `x ≤ (a/x² + 2x)/3 ↔ x³ ≤ a`. -/
private theorem nat_iter_cbrt_ge_self_iff (a x : Nat) (hx : 0 < x) :
    x ≤ (a / (x*x) + 2*x) / 3 ↔ x * x * x ≤ a := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  constructor
  · intro h
    -- 3x ≤ a/(x²) + 2x, so a/(x²) ≥ x, so a ≥ x*(x²) = x³.
    have h_3x : 3 * x ≤ 3 * ((a / (x*x) + 2*x) / 3) := Nat.mul_le_mul_left 3 h
    have h_div_le : 3 * ((a / (x*x) + 2*x) / 3) ≤ a / (x*x) + 2*x := by
      have h_div_mod := Nat.div_add_mod (a / (x*x) + 2*x) 3
      omega
    have h_q_ge : a / (x*x) ≥ x := by omega
    -- a ≥ a/(x*x) * (x*x) ≥ x * (x*x) = x³
    have h_a_ge : a ≥ a / (x*x) * (x*x) := Nat.div_mul_le_self a (x*x)
    have h_mul_ge : a / (x*x) * (x*x) ≥ x * (x*x) := Nat.mul_le_mul_right (x*x) h_q_ge
    have h_xx_x : x * (x*x) = x * x * x := by rw [← Nat.mul_assoc]
    omega
  · intro h_x3_le
    -- a ≥ x³, so a/(x²) ≥ x. Then (a/x² + 2x)/3 ≥ (x + 2x)/3 = x.
    have h_x3 : x * x * x = x * (x*x) := by rw [Nat.mul_assoc]
    have h_a_ge_xxx : x * (x*x) ≤ a := by rw [← h_x3]; exact h_x3_le
    have h_q_ge : a / (x*x) ≥ x := by
      have h_div_ge : (x * (x*x)) / (x*x) ≤ a / (x*x) := Nat.div_le_div_right h_a_ge_xxx
      have h_self : x * (x*x) / (x*x) = x := Nat.mul_div_cancel x hxx_pos
      omega
    -- 3x ≤ a/(x²) + 2x, so (a/(x²) + 2x)/3 ≥ x.
    have h_sum_ge : a / (x*x) + 2*x ≥ 3 * x := by omega
    have h_div_ge : (a / (x*x) + 2*x) / 3 ≥ (3 * x) / 3 := Nat.div_le_div_right h_sum_ge
    have h_simp : (3 * x) / 3 = x := by
      rw [Nat.mul_comm]; exact Nat.mul_div_cancel x (by decide)
    omega

/-- Loop-down descent: if `x³ > a` then `(a/x² + 2x)/3 < x`. -/
private theorem nat_iter_cbrt_lt_self_of_cube_gt (a x : Nat) (hx : 0 < x)
    (h_cube_gt : a < x * x * x) :
    (a / (x*x) + 2*x) / 3 < x := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  -- a < x³, so a/(x²) < x. Then a/(x²) + 2x < 3x, so (a/(x²) + 2x)/3 < x.
  have h_q_lt : a / (x*x) < x := by
    rcases Nat.lt_or_ge (a / (x*x)) x with h | h
    · exact h
    · exfalso
      have h_mul : x * (x*x) ≤ a / (x*x) * (x*x) := Nat.mul_le_mul_right (x*x) h
      have h_div_le : a / (x*x) * (x*x) ≤ a := Nat.div_mul_le_self a (x*x)
      have h_xxx : x * (x*x) = x*x*x := by rw [← Nat.mul_assoc]
      omega
  have h_sum_lt : a / (x*x) + 2*x < 3 * x := by omega
  -- Use the contrapositive: assume (a/x²+2x)/3 ≥ x and derive contradiction.
  rcases Nat.lt_or_ge ((a / (x*x) + 2*x) / 3) x with h | h
  · exact h
  · exfalso
    have h_3x : 3 * x ≤ 3 * ((a / (x*x) + 2*x) / 3) := Nat.mul_le_mul_left 3 h
    have h_div_le : 3 * ((a / (x*x) + 2*x) / 3) ≤ a / (x*x) + 2*x := by
      have h_div_mod := Nat.div_add_mod (a / (x*x) + 2*x) 3
      omega
    omega

/-- Cube expansion: `(y+1)³ = y³ + 3y² + 3y + 1`. -/
private theorem nat_succ_cube (y : Nat) :
    (y + 1) * (y + 1) * (y + 1) = y * y * y + 3 * (y * y) + 3 * y + 1 := by
  have h_sq : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
    have h := nat_sq_expand y 1
    have h_y1 : y * 1 = y := Nat.mul_one y
    have h_1 : (1 : Nat) * 1 = 1 := rfl
    omega
  rw [h_sq]
  -- (y*y + 2*y + 1) * (y + 1) = (y*y + 2*y + 1)*y + (y*y + 2*y + 1)*1
  have h_e := Nat.mul_add (y * y + 2 * y + 1) y 1
  -- (y*y + 2*y + 1) * y = y*y*y + 2*y*y + y
  have h_e1 := Nat.add_mul (y * y + 2 * y) 1 y
  have h_e2 := Nat.add_mul (y * y) (2 * y) y
  have h_2yy : (2 * y) * y = 2 * (y * y) := by
    rw [Nat.mul_assoc]
  have h_1y : (1 : Nat) * y = y := Nat.one_mul _
  have h_e_one : (y * y + 2 * y + 1) * 1 = y * y + 2 * y + 1 := Nat.mul_one _
  omega

/-- `Nat.log2 n ≤ 63` whenever `1 ≤ n < 2^64`. -/
private theorem nat_log2_le_63 (n : Nat) (h_pos : 0 < n) (h_lt : n < 2 ^ 64) :
    Nat.log2 n ≤ 63 := by
  have h_lt' : Nat.log2 n < 64 :=
    (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h_pos)).mpr h_lt
  omega

/-- `2 ^ Nat.log2 n ≤ n` for `n ≥ 1`. -/
private theorem nat_pow_log2_le (n : Nat) (h_pos : 0 < n) : 2 ^ Nat.log2 n ≤ n := by
  rcases Nat.lt_or_ge n (2 ^ Nat.log2 n) with h | h
  · exfalso
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h_pos)).mpr h
    omega
  · exact h

/-- `n < 2 ^ (Nat.log2 n + 1)` for `n ≥ 1`. -/
private theorem nat_lt_pow_succ_log2 (n : Nat) (h_pos : 0 < n) :
    n < 2 ^ (Nat.log2 n + 1) := by
  have h_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp h_pos
  exact (Nat.log2_lt h_ne).mp (Nat.lt_succ_self _)

/-! ## `log2_floor_rec` correctness.

Same proof shape as `log2_rec_correct` in
`proof_patterns/sqrt_u64_modified`; this is the direct port. -/

/-- `log2_floor_rec y count = RustM.ok (count + Nat.log2 y.toNat)` when
    the accumulator doesn't overflow. For `y.toNat ≤ 2^64 - 1`,
    `Nat.log2 y.toNat ≤ 63`. -/
private theorem log2_floor_rec_correct (y : u64) (count : u32)
    (h_no_ovf : count.toNat + Nat.log2 y.toNat < 2 ^ 32) :
    cbrt_u64.log2_floor_rec y count
      = RustM.ok (UInt32.ofNat (count.toNat + Nat.log2 y.toNat)) := by
  induction hk : y.toNat using Nat.strongRecOn generalizing y count with
  | _ k ih =>
    unfold cbrt_u64.log2_floor_rec
    show ((y <=? (1 : u64)) >>= _) = _
    have h_le_eqq : (y <=? (1 : u64) : RustM Bool) = pure (decide (y ≤ 1)) := rfl
    rw [h_le_eqq]
    simp only [pure_bind]
    subst hk
    by_cases hle : y ≤ 1
    · -- Base case
      simp only [decide_eq_true hle, if_true]
      have hyN_le : y.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp hle
      have h_log_zero : Nat.log2 y.toNat = 0 := by
        rcases Nat.lt_or_ge y.toNat 2 with h | h
        · rw [show y.toNat.log2 = if 2 ≤ y.toNat then (y.toNat / 2).log2 + 1 else 0
              from Nat.log2_def y.toNat, if_neg (Nat.not_le.mpr h)]
        · omega
      show RustM.ok count = RustM.ok _
      congr 1
      apply UInt32.toNat_inj.mp
      rw [h_log_zero, Nat.add_zero,
          UInt32.toNat_ofNat_of_lt' (by omega : count.toNat < 2 ^ 32)]
    · -- Step case
      simp only [decide_eq_false hle, Bool.false_eq_true, if_false]
      have h_y_ge_2 : 2 ≤ y.toNat := by
        have h_not_le : ¬ y.toNat ≤ 1 := fun h => hle (UInt64.le_iff_toNat_le.mpr h)
        omega
      have h_shr : (y >>>? (1 : i32) : RustM u64) = pure (y >>> (1 : UInt64)) := by
        show (rust_primitives.ops.bit.Shr.shr y (1 : i32) : RustM u64) =
             pure (y >>> (1 : UInt64))
        show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
                pure (y >>> ((1 : Int32).toNatClampNeg.toUInt64))
              else .fail .integerOverflow) = pure (y >>> (1 : UInt64))
        rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
        simp only [if_true]
        have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
        rw [this]
      rw [h_shr]
      simp only [pure_bind]
      have h_log_ge_one : 1 ≤ Nat.log2 y.toNat := by
        rw [show y.toNat.log2 = if 2 ≤ y.toNat then (y.toNat / 2).log2 + 1 else 0
            from Nat.log2_def y.toNat, if_pos h_y_ge_2]
        omega
      have h_count_lt : count.toNat + 1 < 2 ^ 32 := by omega
      have h_add : (count +? (1 : u32) : RustM u32) = pure (count + 1) := by
        show (rust_primitives.ops.arith.Add.add count (1 : u32) : RustM u32) =
             pure (count + 1)
        show (if BitVec.uaddOverflow count.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (count + 1)) = pure (count + 1)
        have h_no_ovf' : BitVec.uaddOverflow count.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.uaddOverflow count.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow count (1 : u32) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            have h1 : (1 : UInt32).toNat = 1 := rfl
            rw [h1] at this
            omega
        rw [h_no_ovf']
        rfl
      rw [h_add]
      simp only [pure_bind]
      have h_yshr : (y >>> (1 : UInt64)).toNat = y.toNat / 2 := by
        rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
        show y.toNat >>> (1 % 64) = _
        rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
            show (2 ^ 1 : Nat) = 2 from rfl]
      have h_yshr_lt : (y >>> (1 : UInt64)).toNat < y.toNat := by
        rw [h_yshr]
        exact Nat.div_lt_self (by omega) (by decide)
      have h_cplus : (count + (1 : u32)).toNat = count.toNat + 1 := by
        apply UInt32.toNat_add_of_lt
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [h1]; omega
      have h_log_split : Nat.log2 y.toNat = Nat.log2 (y.toNat / 2) + 1 := by
        rw [show y.toNat.log2 = if 2 ≤ y.toNat then (y.toNat / 2).log2 + 1 else 0
            from Nat.log2_def y.toNat, if_pos h_y_ge_2]
      have h_ih_no_ovf : (count + 1).toNat + Nat.log2 (y >>> (1 : UInt64)).toNat < 2 ^ 32 := by
        rw [h_cplus, h_yshr]
        have : Nat.log2 y.toNat = Nat.log2 (y.toNat / 2) + 1 := h_log_split
        omega
      rw [ih _ h_yshr_lt _ (count + 1) h_ih_no_ovf rfl]
      apply congrArg RustM.ok
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat_of_lt' (by omega : (count + 1).toNat + Nat.log2 (y >>> (1 : UInt64)).toNat < 2 ^ 32)]
      rw [UInt32.toNat_ofNat_of_lt' (by omega : count.toNat + Nat.log2 y.toNat < 2 ^ 32)]
      rw [h_cplus, h_yshr, h_log_split]
      omega

/-! ## `pow2_loop` correctness.

`pow2_loop k i g` computes `g * 2^(k - i)` by doubling `g` each step. -/

/-- Reduction of `(g : u64) <<<? (1 : i32)` to `pure (g <<< 1)`.
    Same shape as `h_shr` used inside `log2_floor_rec_correct`. -/
private theorem u64_shl_i32_one (g : UInt64) :
    ((g <<<? (1 : i32)) : RustM u64) = pure (g <<< (1 : UInt64)) := by
  show (rust_primitives.ops.bit.Shl.shl g (1 : i32) : RustM u64) =
       pure (g <<< (1 : UInt64))
  show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
          pure (g <<< ((1 : Int32).toNatClampNeg.toUInt64))
        else .fail .integerOverflow) = pure (g <<< (1 : UInt64))
  rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
  simp only [if_true]
  have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
  rw [this]

/-- `pow2_loop k i g = RustM.ok (g * 2^(k - i))` provided no overflow. -/
private theorem pow2_loop_correct (k i : u32) (g : u64)
    (h_i_le : i.toNat ≤ k.toNat)
    (h_k_le : k.toNat ≤ 63)
    (h_no_ovf : g.toNat * 2 ^ (k.toNat - i.toNat) < 2 ^ 64) :
    ∃ g' : u64, cbrt_u64.pow2_loop k i g = RustM.ok g' ∧
      g'.toNat = g.toNat * 2 ^ (k.toNat - i.toNat) := by
  -- Strong induction on (k - i).
  induction hd : k.toNat - i.toNat using Nat.strongRecOn generalizing i g with
  | _ d ih =>
    subst hd
    unfold cbrt_u64.pow2_loop
    have h_ge_eqq : (i >=? k : RustM Bool) = pure (decide (i ≥ k)) := rfl
    rw [h_ge_eqq]
    simp only [pure_bind]
    by_cases h_ge : i ≥ k
    · -- Base case: i ≥ k, return g. Then k - i = 0, so g' = g * 2^0 = g.
      simp only [decide_eq_true h_ge, if_true]
      have h_i_ge_N : i.toNat ≥ k.toNat := UInt32.le_iff_toNat_le.mp h_ge
      have h_diff_zero : k.toNat - i.toNat = 0 := by omega
      refine ⟨g, rfl, ?_⟩
      rw [h_diff_zero]
      simp
    · -- Step case: i < k, recurse with (i+1, g << 1).
      simp only [decide_eq_false h_ge, Bool.false_eq_true, if_false]
      have h_i_lt : i.toNat < k.toNat := by
        have h_not : ¬ k.toNat ≤ i.toNat := fun hh => h_ge (UInt32.le_iff_toNat_le.mpr hh)
        omega
      have h_diff_pos : 0 < k.toNat - i.toNat := by omega
      -- i + 1 doesn't overflow since i < k ≤ 63 < 2^32.
      have h_i_lt_63 : i.toNat < 63 := by omega
      have h_add : (i +? (1 : u32) : RustM u32) = pure (i + 1) := by
        show (rust_primitives.ops.arith.Add.add i (1 : u32) : RustM u32) = pure (i + 1)
        show (if BitVec.uaddOverflow i.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (i + 1)) = pure (i + 1)
        have h_no_ovf' : BitVec.uaddOverflow i.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.uaddOverflow i.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow i (1 : u32) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            have h1 : (1 : UInt32).toNat = 1 := rfl
            rw [h1] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      rw [u64_shl_i32_one g]
      simp only [pure_bind]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := by
        apply UInt32.toNat_add_of_lt
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [h1]; omega
      -- (g <<< 1).toNat = g.toNat * 2 mod 2^64. For g * 2 < 2^64, equals g.toNat * 2.
      have h_g_mul_2 : g.toNat * 2 < 2 ^ 64 := by
        -- g * 2^(k - i) < 2^64 and 2^(k - i) ≥ 2 since k - i ≥ 1, so g * 2 ≤ g * 2^(k - i) < 2^64.
        have h_pow_ge : (2 : Nat) ^ (k.toNat - i.toNat) ≥ 2 := by
          have h_pow_le : 2 ^ 1 ≤ 2 ^ (k.toNat - i.toNat) := by
            apply Nat.pow_le_pow_right
            · decide
            · omega
          have h_p1 : (2 : Nat) ^ 1 = 2 := by decide
          omega
        have h_mul_le : g.toNat * 2 ≤ g.toNat * 2 ^ (k.toNat - i.toNat) :=
          Nat.mul_le_mul_left _ h_pow_ge
        omega
      have h_shl_toNat : (g <<< (1 : UInt64)).toNat = g.toNat * 2 := by
        rw [UInt64.toNat_shiftLeft]
        show g.toNat <<< (1 % 64) % 2 ^ 64 = g.toNat * 2
        rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftLeft_eq, show (2 ^ 1 : Nat) = 2 from rfl]
        exact Nat.mod_eq_of_lt h_g_mul_2
      -- New measure: k - (i+1) = (k - i) - 1.
      have h_new_diff : k.toNat - (i + 1).toNat = (k.toNat - i.toNat) - 1 := by
        rw [h_i1_toNat]; omega
      have h_new_lt : k.toNat - (i + 1).toNat < k.toNat - i.toNat := by
        rw [h_new_diff]; omega
      -- New no_ovf: (g << 1).toNat * 2^((k.toNat - i.toNat) - 1) = g.toNat * 2 * 2^((k.toNat - i.toNat) - 1)
      --   = g.toNat * 2^(k.toNat - i.toNat). So same bound.
      have h_pow_identity : g.toNat * 2 * 2 ^ ((k.toNat - i.toNat) - 1)
          = g.toNat * 2 ^ (k.toNat - i.toNat) := by
        have h_pow_split : 2 * 2 ^ ((k.toNat - i.toNat) - 1) = 2 ^ (k.toNat - i.toNat) := by
          have h_eq : 2 ^ ((k.toNat - i.toNat) - 1 + 1) = 2 * 2 ^ ((k.toNat - i.toNat) - 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
          have h_simp : (k.toNat - i.toNat) - 1 + 1 = k.toNat - i.toNat := by omega
          rw [h_simp] at h_eq
          exact h_eq.symm
        rw [Nat.mul_assoc, h_pow_split]
      have h_new_no_ovf : (g <<< (1 : UInt64)).toNat * 2 ^ (k.toNat - (i + 1).toNat) < 2 ^ 64 := by
        rw [h_shl_toNat, h_new_diff, h_pow_identity]
        exact h_no_ovf
      have h_new_i_le : (i + 1).toNat ≤ k.toNat := by rw [h_i1_toNat]; omega
      obtain ⟨g', hg'_eq, hg'_toNat⟩ :=
        ih (k.toNat - (i + 1).toNat) h_new_lt (i + 1) (g <<< (1 : UInt64))
          h_new_i_le h_new_no_ovf rfl
      refine ⟨g', hg'_eq, ?_⟩
      rw [hg'_toNat, h_shl_toNat, h_new_diff, h_pow_identity]

/-! ## icbrt2 correctness for `cbrt_u32_loop`.

The Hacker's-Delight `icbrt2` algorithm maintains the invariant
`y³ · 8^s_iter ≤ a_orig < (y+1)³ · 8^s_iter` at each iteration, with
`y2 = y²` and the encoded remainder relation `x = a_orig - y³ · 8^s_iter`.

For the proof to go through, we additionally establish overflow safety
for every u32 arithmetic step from the bound `y < 2^11` (itself derived
from `y³ ≤ y³ · 8^s_iter ≤ a_orig < 2^32`).

The mathematical core: in one iteration of the loop,
  * `s_iter_new := s_iter - 1`, `s := 3 · s_iter_new`.
  * `y2_d := 4y² = (2y)²`, `y_d := 2y`, `b := 12y² + 6y + 1`.
  * Key cubic identity: `(2y+1)³ = 8y³ + b`.
  * Bridge: `(x >>> s) ≥ b ↔ b · 2^s ≤ x` (`Nat.le_div_iff` shape).
  * True branch: `y_new := 2y+1`, `x_new := x − b·2^s`.
    New invariants hold because `(2y+1)³·8^s_iter_new = (8y³+b)·8^s_iter_new
    = y³·8^s_iter + b·2^s ≤ x + y³·8^s_iter = a_orig`.
  * False branch: `y_new := 2y`. New invariants hold because
    `(2y+1)³·8^s_iter_new = y³·8^s_iter + b·2^s > y³·8^s_iter + x = a_orig`. -/

/-- Helper: `b ≤ n / c ↔ b · c ≤ n` for positive `c`. Used to bridge the
    `(x >>> s) ≥? b` test against the abstract `b · 2^s ≤ x` form. -/
private theorem nat_div_ge_iff_mul_le (b n c : Nat) (hc : 0 < c) :
    b ≤ n / c ↔ b * c ≤ n := by
  constructor
  · intro h
    have h1 : b * c ≤ (n / c) * c := Nat.mul_le_mul_right c h
    have h2 : (n / c) * c ≤ n := Nat.div_mul_le_self n c
    omega
  · intro h
    rcases Nat.lt_or_ge (n / c) b with h_lt | h_ge
    · exfalso
      have h_le' : n / c + 1 ≤ b := h_lt
      have h_mul : (n / c + 1) * c ≤ b * c := Nat.mul_le_mul_right c h_le'
      have h_mod_lt : n % c < c := Nat.mod_lt _ hc
      have h_div_mod : c * (n / c) + n % c = n := Nat.div_add_mod n c
      have h_swap : (n / c) * c = c * (n / c) := Nat.mul_comm _ _
      have h_dist : (n / c + 1) * c = (n / c) * c + c := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · exact h_ge

/-- Helper: `(2y)·(2y) = 4·y²`. Used to expand `(2y+1)²` and `(2y+1)³`. -/
private theorem nat_two_y_sq (y : Nat) : (2 * y) * (2 * y) = 4 * (y * y) := by
  rw [Nat.mul_assoc 2 y (2 * y), Nat.mul_comm y (2 * y),
      Nat.mul_assoc 2 y y, ← Nat.mul_assoc]

/-- Helper: `(2y)·(2y)·(2y) = 8·y³`. Used to expand `(2y+1)³`. -/
private theorem nat_two_y_cube (y : Nat) :
    (2 * y) * (2 * y) * (2 * y) = 8 * (y * y * y) := by
  rw [nat_two_y_sq, Nat.mul_assoc 4 (y * y) (2 * y)]
  have h_yy_2y : y * y * (2 * y) = 2 * (y * y * y) := by
    rw [← Nat.mul_assoc (y*y) 2 y, Nat.mul_comm (y*y) 2, Nat.mul_assoc]
  rw [h_yy_2y, ← Nat.mul_assoc]

/-- `(2y+1)² = 4y² + 4y + 1`. -/
private theorem nat_2y1_sq (y : Nat) :
    (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by
  have h := nat_sq_expand (2 * y) 1
  have h_4yy : (2 * y) * (2 * y) = 4 * (y * y) := nat_two_y_sq y
  have h_4y : 2 * ((2 * y) * 1) = 4 * y := by
    rw [Nat.mul_one, ← Nat.mul_assoc]
  rw [h_4yy, h_4y, show (1 : Nat) * 1 = 1 from rfl] at h
  exact h

/-- `(2y+1)³ = 8y³ + 12y² + 6y + 1`. The key cubic identity for the
    Hacker's-Delight icbrt2 step. -/
private theorem nat_2y1_cube (y : Nat) :
    (2 * y + 1) * (2 * y + 1) * (2 * y + 1) =
    8 * (y * y * y) + 12 * (y * y) + 6 * y + 1 := by
  have h := nat_cube_expand (2 * y) 1
  have h_8y3 : (2 * y) * (2 * y) * (2 * y) = 8 * (y * y * y) := nat_two_y_cube y
  have h_4yy_1 : (2 * y) * (2 * y) * 1 = 4 * (y * y) := by
    rw [Nat.mul_one]; exact nat_two_y_sq y
  have h_2y_11 : (2 * y) * 1 * 1 = 2 * y := by rw [Nat.mul_one, Nat.mul_one]
  have h_111 : (1 : Nat) * 1 * 1 = 1 := rfl
  rw [h_8y3, h_4yy_1, h_2y_11, h_111] at h
  rw [h]
  rw [show 3 * (4 * (y * y)) = 12 * (y * y) from by rw [← Nat.mul_assoc]]
  rw [show 3 * (2 * y) = 6 * y from by rw [← Nat.mul_assoc]]

/-- Hacker's-Delight `icbrt2` loop correctness. Proven by strong induction
    on `s_iter.toNat`. The recursive case discharges u32 overflow at every
    arithmetic step from the bound `y < 2^11` (derived from the invariant
    `y³ · 8^s_iter ≤ a_orig < 2^32`), then propagates the four invariants
    `y2 = y²`, `y³·8^s_iter ≤ a`, `a < (y+1)³·8^s_iter`, `x = a − y³·8^s_iter`
    through both branches of `(x >>> s) ≥ b`. -/
private theorem cbrt_u32_loop_correct
    (s_iter : u32) (x : u32) (y2 : u32) (y : u32) (a_orig : Nat)
    (h_a_lt : a_orig < 2 ^ 32)
    (h_s_le_11 : s_iter.toNat ≤ 11)
    (h_y2_eq : y2.toNat = y.toNat * y.toNat)
    (h_y_cube_le : y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat ≤ a_orig)
    (h_a_lt_succ_cube : a_orig <
      (y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1) * 8 ^ s_iter.toNat)
    (h_x_eq : x.toNat = a_orig - y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat) :
    ∃ y' : u32, cbrt_u64.cbrt_u32_loop s_iter x y2 y = RustM.ok y' ∧
      y'.toNat * y'.toNat * y'.toNat ≤ a_orig ∧
      a_orig < (y'.toNat + 1) * (y'.toNat + 1) * (y'.toNat + 1) := by
  -- Strong induction on s_iter.toNat.
  induction hk : s_iter.toNat using Nat.strongRecOn generalizing s_iter x y2 y with
  | _ k ih =>
    subst hk
    unfold cbrt_u64.cbrt_u32_loop
    have h_eq_eqq : (s_iter ==? (0 : u32) : RustM Bool) = pure (decide (s_iter = 0)) := rfl
    rw [h_eq_eqq]
    simp only [pure_bind]
    by_cases h_zero : s_iter = 0
    · -- Base case: s_iter = 0, return y.
      simp only [decide_eq_true h_zero, if_true]
      refine ⟨y, rfl, ?_, ?_⟩
      · -- y³ * 8^0 = y³ ≤ a_orig
        have h_s0 : s_iter.toNat = 0 := by rw [h_zero]; rfl
        rw [h_s0] at h_y_cube_le
        simp at h_y_cube_le
        exact h_y_cube_le
      · -- a_orig < (y+1)³ * 8^0 = (y+1)³
        have h_s0 : s_iter.toNat = 0 := by rw [h_zero]; rfl
        rw [h_s0] at h_a_lt_succ_cube
        simp at h_a_lt_succ_cube
        exact h_a_lt_succ_cube
    · -- Recursive case: s_iter > 0.
      simp only [decide_eq_false h_zero, Bool.false_eq_true, if_false]
      -- Bound y: from y³·8^s ≤ a_orig < 2^32 we get y < 2^11 = 2048.
      have h_y_lt_2048 : y.toNat < 2048 := by
        rcases Nat.lt_or_ge y.toNat 2048 with hlt | hge
        · exact hlt
        · exfalso
          have h_y3 : 2048 * 2048 * 2048 ≤ y.toNat * y.toNat * y.toNat :=
            Nat.mul_le_mul (Nat.mul_le_mul hge hge) hge
          have h_8s_pos : 1 ≤ 8 ^ s_iter.toNat :=
            Nat.one_le_iff_ne_zero.mpr
              (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide : 0 < 8)))
          have h_mul : 2048 * 2048 * 2048 * 1 ≤
              y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat :=
            Nat.mul_le_mul h_y3 h_8s_pos
          rw [Nat.mul_one] at h_mul
          have h_compute : 2048 * 2048 * 2048 = 8589934592 := by decide
          have h_2_32 : (2 : Nat) ^ 32 = 4294967296 := by decide
          omega
      have h_s_pos : 1 ≤ s_iter.toNat := by
        rcases Nat.eq_zero_or_pos s_iter.toNat with h | h
        · exfalso
          apply h_zero
          apply UInt32.toNat_inj.mp
          rw [h]; rfl
        · exact h
      -- Constants.
      have h_1_toNat : ((1 : u32)).toNat = 1 := rfl
      have h_2_toNat : ((2 : u32)).toNat = 2 := rfl
      have h_3_toNat : ((3 : u32)).toNat = 3 := rfl
      have h_4_toNat : ((4 : u32)).toNat = 4 := rfl
      -- Step 1: s_iter -? 1 = pure (s_iter - 1).
      have h_sub_step : (s_iter -? (1 : u32) : RustM u32) = pure (s_iter - 1) := by
        show (rust_primitives.ops.arith.Sub.sub s_iter (1 : u32) : RustM u32) =
             pure (s_iter - 1)
        show (if BitVec.usubOverflow s_iter.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (s_iter - 1)) = pure (s_iter - 1)
        have h_no_ovf : BitVec.usubOverflow s_iter.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.usubOverflow s_iter.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.subOverflow s_iter (1 : u32) = true := h_eq
            rw [UInt32.subOverflow_iff] at this
            rw [h_1_toNat] at this
            omega
        rw [h_no_ovf]; rfl
      rw [h_sub_step]
      simp only [pure_bind]
      have h_sn_toNat : (s_iter - (1 : u32)).toNat = s_iter.toNat - 1 := by
        apply UInt32.toNat_sub_of_le'
        rw [h_1_toNat]; omega
      have h_sn_le_10 : (s_iter - (1 : u32)).toNat ≤ 10 := by rw [h_sn_toNat]; omega
      -- Step 2: (s_iter - 1) *? 3 = pure ((s_iter - 1) * 3).
      have h_mul_3 : ((s_iter - (1 : u32)) *? (3 : u32) : RustM u32) =
                     pure ((s_iter - 1) * 3) := by
        show (rust_primitives.ops.arith.Mul.mul (s_iter - 1) (3 : u32) : RustM u32) =
             pure ((s_iter - 1) * 3)
        show (if BitVec.umulOverflow (s_iter - 1).toBitVec (3 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure ((s_iter - 1) * 3)) = _
        have h_no_ovf : BitVec.umulOverflow (s_iter - 1).toBitVec ((3 : u32).toBitVec) = false := by
          cases h_eq : BitVec.umulOverflow (s_iter - 1).toBitVec ((3 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow (s_iter - 1) (3 : u32) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_3_toNat] at this
            have h_le : (s_iter - 1).toNat * 3 ≤ 10 * 3 := Nat.mul_le_mul_right 3 h_sn_le_10
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_3]
      simp only [pure_bind]
      have h_s_toNat : ((s_iter - (1 : u32)) * (3 : u32)).toNat = (s_iter.toNat - 1) * 3 := by
        rw [UInt32.toNat_mul_of_lt, h_sn_toNat, h_3_toNat]
        rw [h_3_toNat]
        have h_le : (s_iter - 1).toNat * 3 ≤ 10 * 3 := Nat.mul_le_mul_right 3 h_sn_le_10
        rw [h_sn_toNat] at h_le; omega
      have h_s_le_30 : ((s_iter - (1 : u32)) * (3 : u32)).toNat ≤ 30 := by
        rw [h_s_toNat]; omega
      -- Step 3: y2 *? 4 = pure (y2 * 4). y2 < 2^22 (from y < 2048).
      have h_y2_lt : y2.toNat < 2 ^ 22 := by
        rw [h_y2_eq]
        have h_le : y.toNat * y.toNat ≤ 2047 * 2047 :=
          Nat.mul_le_mul (by omega) (by omega)
        have h_c : 2047 * 2047 < (2 : Nat) ^ 22 := by decide
        omega
      have h_mul_4 : (y2 *? (4 : u32) : RustM u32) = pure (y2 * 4) := by
        show (rust_primitives.ops.arith.Mul.mul y2 (4 : u32) : RustM u32) = pure (y2 * 4)
        show (if BitVec.umulOverflow y2.toBitVec (4 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (y2 * 4)) = _
        have h_no_ovf : BitVec.umulOverflow y2.toBitVec ((4 : u32).toBitVec) = false := by
          cases h_eq : BitVec.umulOverflow y2.toBitVec ((4 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow y2 (4 : u32) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_4_toNat] at this
            have h_le : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
            have h_c : ((2 : Nat) ^ 22 - 1) * 4 < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_4]
      simp only [pure_bind]
      have h_y2d_toNat : (y2 * (4 : u32)).toNat = y2.toNat * 4 := by
        apply UInt32.toNat_mul_of_lt
        rw [h_4_toNat]
        have h_le : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_c : ((2 : Nat) ^ 22 - 1) * 4 < 2 ^ 32 := by decide
        omega
      -- Step 4: y *? 2 = pure (y * 2).
      have h_mul_2 : (y *? (2 : u32) : RustM u32) = pure (y * 2) := by
        show (rust_primitives.ops.arith.Mul.mul y (2 : u32) : RustM u32) = pure (y * 2)
        show (if BitVec.umulOverflow y.toBitVec (2 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (y * 2)) = _
        have h_no_ovf : BitVec.umulOverflow y.toBitVec ((2 : u32).toBitVec) = false := by
          cases h_eq : BitVec.umulOverflow y.toBitVec ((2 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow y (2 : u32) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_2_toNat] at this
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_2]
      simp only [pure_bind]
      have h_yd_toNat : (y * (2 : u32)).toNat = y.toNat * 2 := by
        apply UInt32.toNat_mul_of_lt
        rw [h_2_toNat]; omega
      -- Step 5: y2_d +? y_d.
      have h_add_y2d_yd : (y2 * 4 +? y * 2 : RustM u32) = pure (y2 * 4 + y * 2) := by
        show (rust_primitives.ops.arith.Add.add (y2 * 4) (y * 2) : RustM u32) = _
        show (if BitVec.uaddOverflow (y2 * 4).toBitVec (y * 2).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (y2 * 4 + y * 2)) = _
        have h_no_ovf : BitVec.uaddOverflow (y2 * 4).toBitVec (y * 2).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (y2 * 4).toBitVec (y * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow (y2 * 4) (y * 2) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            rw [h_y2d_toNat, h_yd_toNat] at this
            have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
            have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2 < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_add_y2d_yd]
      simp only [pure_bind]
      have h_sum_toNat : (y2 * 4 + y * 2).toNat = y2.toNat * 4 + y.toNat * 2 := by
        rw [UInt32.toNat_add_of_lt]
        · rw [h_y2d_toNat, h_yd_toNat]
        rw [h_y2d_toNat, h_yd_toNat]
        have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2 < 2 ^ 32 := by decide
        omega
      have h_sum_lt : (y2 * 4 + y * 2).toNat ≤ (2 ^ 22 - 1) * 4 + 2047 * 2 := by
        rw [h_sum_toNat]
        have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_le3 : y.toNat * 2 ≤ 2047 * 2 := Nat.mul_le_mul_right 2 (by omega)
        omega
      -- Step 6: 3 *? (y2_d + y_d).
      have h_mul_3_sum : ((3 : u32) *? (y2 * 4 + y * 2) : RustM u32) =
                        pure (3 * (y2 * 4 + y * 2)) := by
        show (rust_primitives.ops.arith.Mul.mul (3 : u32) (y2 * 4 + y * 2) : RustM u32) = _
        show (if BitVec.umulOverflow (3 : u32).toBitVec (y2 * 4 + y * 2).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (3 * (y2 * 4 + y * 2))) = _
        have h_no_ovf : BitVec.umulOverflow (3 : u32).toBitVec (y2 * 4 + y * 2).toBitVec = false := by
          cases h_eq : BitVec.umulOverflow (3 : u32).toBitVec (y2 * 4 + y * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow (3 : u32) (y2 * 4 + y * 2) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_3_toNat] at this
            have h_le : 3 * (y2 * 4 + y * 2).toNat ≤ 3 * ((2 ^ 22 - 1) * 4 + 2047 * 2) :=
              Nat.mul_le_mul_left 3 h_sum_lt
            have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_3_sum]
      simp only [pure_bind]
      have h_3sum_toNat : ((3 : u32) * (y2 * 4 + y * 2)).toNat =
                         3 * (y2.toNat * 4 + y.toNat * 2) := by
        rw [UInt32.toNat_mul_of_lt]
        · rw [h_3_toNat, h_sum_toNat]
        rw [h_3_toNat]
        have h_le : 3 * (y2 * 4 + y * 2).toNat ≤ 3 * ((2 ^ 22 - 1) * 4 + 2047 * 2) :=
          Nat.mul_le_mul_left 3 h_sum_lt
        have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) < 2 ^ 32 := by decide
        omega
      have h_3sum_lt : ((3 : u32) * (y2 * 4 + y * 2)).toNat ≤
                       3 * ((2 ^ 22 - 1) * 4 + 2047 * 2) := by
        rw [h_3sum_toNat]
        have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_le3 : y.toNat * 2 ≤ 2047 * 2 := Nat.mul_le_mul_right 2 (by omega)
        omega
      -- Step 7: (...) +? 1.
      have h_add_b_1 : ((3 : u32) * (y2 * 4 + y * 2) +? (1 : u32) : RustM u32) =
                       pure (3 * (y2 * 4 + y * 2) + 1) := by
        show (rust_primitives.ops.arith.Add.add (3 * (y2 * 4 + y * 2)) (1 : u32) : RustM u32) = _
        show (if BitVec.uaddOverflow (3 * (y2 * 4 + y * 2)).toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (_)) = _
        have h_no_ovf : BitVec.uaddOverflow (3 * (y2 * 4 + y * 2)).toBitVec (1 : u32).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (3 * (y2 * 4 + y * 2)).toBitVec (1 : u32).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow (3 * (y2 * 4 + y * 2)) (1 : u32) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            rw [h_1_toNat] at this
            have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) + 1 < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_add_b_1]
      simp only [pure_bind]
      have h_b_toNat : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat =
                      3 * (y2.toNat * 4 + y.toNat * 2) + 1 := by
        rw [UInt32.toNat_add_of_lt]
        · rw [h_3sum_toNat, h_1_toNat]
        rw [h_3sum_toNat, h_1_toNat]
        have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) + 1 < 2 ^ 32 := by decide
        omega
      -- Algebraic forms.
      have h_y2d_alg : (y2 * (4 : u32)).toNat = 4 * (y.toNat * y.toNat) := by
        rw [h_y2d_toNat, h_y2_eq]; exact Nat.mul_comm _ _
      have h_yd_alg : (y * (2 : u32)).toNat = 2 * y.toNat := by
        rw [h_yd_toNat]; exact Nat.mul_comm _ _
      have h_b_alg : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat
                    = 12 * (y.toNat * y.toNat) + 6 * y.toNat + 1 := by
        rw [h_b_toNat, h_y2_eq,
            show y.toNat * y.toNat * 4 = 4 * (y.toNat * y.toNat) from Nat.mul_comm _ _,
            show y.toNat * 2 = 2 * y.toNat from Nat.mul_comm _ _,
            Nat.mul_add,
            show (3 : Nat) * (4 * (y.toNat * y.toNat)) = 12 * (y.toNat * y.toNat) from by
              rw [← Nat.mul_assoc],
            show (3 : Nat) * (2 * y.toNat) = 6 * y.toNat from by
              rw [← Nat.mul_assoc]]
      -- Key cubic identity: (2y+1)³ = 8y³ + b.
      have h_cube_id : (2 * y.toNat + 1) * (2 * y.toNat + 1) * (2 * y.toNat + 1) =
                       8 * (y.toNat * y.toNat * y.toNat) +
                       (12 * (y.toNat * y.toNat) + 6 * y.toNat + 1) := by
        rw [nat_2y1_cube]
        omega
      -- 8^s_iter = 8 * 8^(s_iter - 1).
      have h_8_split : (8 : Nat) ^ s_iter.toNat =
                       8 * 8 ^ (s_iter.toNat - 1) := by
        have h_eq : s_iter.toNat = (s_iter.toNat - 1) + 1 := by omega
        calc (8 : Nat) ^ s_iter.toNat
            = 8 ^ ((s_iter.toNat - 1) + 1) := by rw [← h_eq]
          _ = 8 ^ (s_iter.toNat - 1) * 8 := Nat.pow_succ 8 _
          _ = 8 * 8 ^ (s_iter.toNat - 1) := Nat.mul_comm _ _
      -- 2^s.toNat = 8^(s_iter - 1).
      have h_2s_eq : (2 : Nat) ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat =
                     8 ^ (s_iter.toNat - 1) := by
        rw [h_s_toNat]
        rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_mul]
        congr 1
        exact Nat.mul_comm _ _
      -- Step 8: x >>>? s = pure (x >>> s) when s < 32.
      have h_shr : (x >>>? ((s_iter - (1 : u32)) * (3 : u32)) : RustM u32) =
                   pure (x >>> ((s_iter - 1) * 3)) := by
        show (rust_primitives.ops.bit.Shr.shr x ((s_iter - 1) * 3) : RustM u32) =
             pure (x >>> ((s_iter - 1) * 3))
        show (if (0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32) then
                pure (x >>> ((s_iter - 1) * 3))
              else (.fail .integerOverflow : RustM u32)) = _
        have h_0_le : (0 : u32) ≤ (s_iter - 1) * 3 :=
          UInt32.le_iff_toNat_le.mpr (by show 0 ≤ _; omega)
        have h_lt_32 : (s_iter - 1) * 3 < (32 : u32) :=
          UInt32.lt_iff_toNat_lt.mpr (by
            show ((s_iter - 1) * 3).toNat < (32 : u32).toNat
            show _ < 32
            omega)
        rw [show ((0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32)) = true from by
              rw [show (decide ((0 : u32) ≤ (s_iter - 1) * 3) = true) from decide_eq_true h_0_le]
              rw [show (decide ((s_iter - 1) * 3 < (32 : u32)) = true) from decide_eq_true h_lt_32]
              rfl]
        rfl
      rw [h_shr]
      simp only [pure_bind]
      have h_xshr_toNat : (x >>> ((s_iter - 1) * 3)).toNat =
                          x.toNat / 2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
        rw [UInt32.toNat_shiftRight]
        show x.toNat >>> (((s_iter - 1) * 3).toNat % 32) = _
        rw [Nat.mod_eq_of_lt (by omega : ((s_iter - 1) * 3).toNat < 32),
            Nat.shiftRight_eq_div_pow]
      -- Step 9: test (x >>> s) >=? b.
      have h_ge_eqq : ((x >>> ((s_iter - 1) * 3)) >=? ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32))
                       : RustM Bool) =
                      pure (decide (x >>> ((s_iter - 1) * 3) ≥
                                    (3 : u32) * (y2 * 4 + y * 2) + (1 : u32))) := rfl
      rw [h_ge_eqq]
      simp only [pure_bind]
      -- Bridge: (x >>> s) ≥ b ↔ b * 2^s ≤ x.
      have h_ge_iff : (x >>> ((s_iter - 1) * 3) ≥
                       (3 : u32) * (y2 * 4 + y * 2) + (1 : u32)) ↔
                      ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                        2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat ≤ x.toNat := by
        show ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)) ≤ x >>> ((s_iter - 1) * 3) ↔ _
        rw [UInt32.le_iff_toNat_le, h_xshr_toNat]
        exact nat_div_ge_iff_mul_le _ _ _ (Nat.pow_pos (by decide : 0 < 2))
      -- Useful: y³ · 8^s_iter rewritten.
      have h_y3_split : y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat =
                        8 * (y.toNat * y.toNat * y.toNat) * 8 ^ (s_iter.toNat - 1) := by
        rw [h_8_split]
        rw [← Nat.mul_assoc (y.toNat * y.toNat * y.toNat) 8 (8 ^ (s_iter.toNat - 1))]
        rw [Nat.mul_comm (y.toNat * y.toNat * y.toNat) 8]
      have h_x_inv : x.toNat + y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat = a_orig := by
        rw [h_x_eq]; omega
      -- Branch on (x >>> s) ≥ b.
      by_cases h_ge : x >>> ((s_iter - 1) * 3) ≥ (3 : u32) * (y2 * 4 + y * 2) + (1 : u32)
      · -- True branch: y_new = 2y+1.
        simp only [decide_eq_true h_ge, if_true]
        have h_x_ge : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                      2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat ≤ x.toNat :=
          h_ge_iff.mp h_ge
        have h_b2s_lt_32 : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                           2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat < 2 ^ 32 := by
          have h_x_lt : x.toNat < 2 ^ 32 := x.toNat_lt
          omega
        -- Step 10: b <<<? s = pure (b <<< s).
        have h_shl_b : (((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)) <<<?
                         ((s_iter - (1 : u32)) * (3 : u32)) : RustM u32) =
                       pure ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)) := by
          show (rust_primitives.ops.bit.Shl.shl
                  (3 * (y2 * 4 + y * 2) + 1) ((s_iter - 1) * 3) : RustM u32) = _
          show (if (0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32) then
                  pure ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))
                else (.fail .integerOverflow : RustM u32)) = _
          have h_0_le : (0 : u32) ≤ (s_iter - 1) * 3 :=
            UInt32.le_iff_toNat_le.mpr (by show 0 ≤ _; omega)
          have h_lt_32 : (s_iter - 1) * 3 < (32 : u32) :=
            UInt32.lt_iff_toNat_lt.mpr (by
              show ((s_iter - 1) * 3).toNat < (32 : u32).toNat
              show _ < 32
              omega)
          rw [show ((0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32)) = true from by
                rw [show (decide ((0 : u32) ≤ (s_iter - 1) * 3) = true) from decide_eq_true h_0_le]
                rw [show (decide ((s_iter - 1) * 3 < (32 : u32)) = true) from decide_eq_true h_lt_32]
                rfl]
          rfl
        rw [h_shl_b]
        simp only [pure_bind]
        have h_bshl_toNat : ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toNat =
                            ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
          rw [UInt32.toNat_shiftLeft]
          show (((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat <<<
                  (((s_iter - 1) * 3).toNat % 32)) % 2 ^ 32 = _
          rw [Nat.mod_eq_of_lt (by omega : ((s_iter - 1) * 3).toNat < 32),
              Nat.shiftLeft_eq]
          exact Nat.mod_eq_of_lt h_b2s_lt_32
        -- Step 11: x -? (b <<< s).
        have h_sub_x : (x -? ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))
                        : RustM u32) =
                       pure (x - ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))) := by
          show (rust_primitives.ops.arith.Sub.sub x
                  ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)) : RustM u32) = _
          show (if BitVec.usubOverflow x.toBitVec
                  ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (_)) = _
          have h_no_ovf : BitVec.usubOverflow x.toBitVec
              ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toBitVec = false := by
            cases h_eq : BitVec.usubOverflow x.toBitVec
              ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.subOverflow x
                ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)) = true := h_eq
              rw [UInt32.subOverflow_iff] at this
              rw [h_bshl_toNat] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_sub_x]
        simp only [pure_bind]
        have h_xnew_toNat : (x - (3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toNat =
                            x.toNat -
                            ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
          rw [UInt32.toNat_sub_of_le' (by rw [h_bshl_toNat]; exact h_x_ge), h_bshl_toNat]
        -- Step 12: 2 *? y_d.
        have h_mul_2_yd : ((2 : u32) *? (y * 2) : RustM u32) = pure (2 * (y * 2)) := by
          show (rust_primitives.ops.arith.Mul.mul (2 : u32) (y * 2) : RustM u32) = _
          show (if BitVec.umulOverflow (2 : u32).toBitVec (y * 2).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (2 * (y * 2))) = _
          have h_no_ovf : BitVec.umulOverflow (2 : u32).toBitVec (y * 2).toBitVec = false := by
            cases h_eq : BitVec.umulOverflow (2 : u32).toBitVec (y * 2).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.mulOverflow (2 : u32) (y * 2) = true := h_eq
              rw [UInt32.mulOverflow_iff] at this
              rw [h_2_toNat, h_yd_toNat] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_mul_2_yd]
        simp only [pure_bind]
        have h_2yd_toNat : ((2 : u32) * (y * 2)).toNat = 2 * (y.toNat * 2) := by
          rw [UInt32.toNat_mul_of_lt]
          · rw [h_2_toNat, h_yd_toNat]
          rw [h_2_toNat, h_yd_toNat]; omega
        -- Step 13: y2_d +? (2 * y_d).
        have h_add_y2new : (y2 * 4 +? (2 : u32) * (y * 2) : RustM u32) =
                           pure (y2 * 4 + 2 * (y * 2)) := by
          show (rust_primitives.ops.arith.Add.add (y2 * 4) ((2 : u32) * (y * 2)) : RustM u32) = _
          show (if BitVec.uaddOverflow (y2 * 4).toBitVec ((2 : u32) * (y * 2)).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (_)) = _
          have h_no_ovf : BitVec.uaddOverflow (y2 * 4).toBitVec ((2 : u32) * (y * 2)).toBitVec = false := by
            cases h_eq : BitVec.uaddOverflow (y2 * 4).toBitVec ((2 : u32) * (y * 2)).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.addOverflow (y2 * 4) ((2 : u32) * (y * 2)) = true := h_eq
              rw [UInt32.addOverflow_iff] at this
              rw [h_y2d_toNat, h_2yd_toNat] at this
              have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
              have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) < 2 ^ 32 := by decide
              omega
          rw [h_no_ovf]; rfl
        rw [h_add_y2new]
        simp only [pure_bind]
        have h_y2new_sum_toNat : (y2 * 4 + (2 : u32) * (y * 2)).toNat =
                                  y2.toNat * 4 + 2 * (y.toNat * 2) := by
          rw [UInt32.toNat_add_of_lt]
          · rw [h_y2d_toNat, h_2yd_toNat]
          rw [h_y2d_toNat, h_2yd_toNat]
          have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
          have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) < 2 ^ 32 := by decide
          omega
        -- Step 14: (...) +? 1.
        have h_add_y2new_1 : ((y2 * 4 + (2 : u32) * (y * 2)) +? (1 : u32) : RustM u32) =
                              pure (y2 * 4 + 2 * (y * 2) + 1) := by
          show (rust_primitives.ops.arith.Add.add
                  (y2 * 4 + (2 : u32) * (y * 2)) (1 : u32) : RustM u32) = _
          show (if BitVec.uaddOverflow (y2 * 4 + (2 : u32) * (y * 2)).toBitVec
                  (1 : u32).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (_)) = _
          have h_no_ovf : BitVec.uaddOverflow (y2 * 4 + (2 : u32) * (y * 2)).toBitVec
                            (1 : u32).toBitVec = false := by
            cases h_eq : BitVec.uaddOverflow (y2 * 4 + (2 : u32) * (y * 2)).toBitVec
                          (1 : u32).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.addOverflow (y2 * 4 + (2 : u32) * (y * 2)) (1 : u32) = true := h_eq
              rw [UInt32.addOverflow_iff] at this
              rw [h_1_toNat, h_y2new_sum_toNat] at this
              have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
              have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) + 1 < 2 ^ 32 := by decide
              omega
          rw [h_no_ovf]; rfl
        rw [h_add_y2new_1]
        simp only [pure_bind]
        have h_y2new_toNat : ((y2 * 4 + (2 : u32) * (y * 2)) + (1 : u32)).toNat =
                              y2.toNat * 4 + 2 * (y.toNat * 2) + 1 := by
          rw [UInt32.toNat_add_of_lt]
          · rw [h_y2new_sum_toNat, h_1_toNat]
          rw [h_y2new_sum_toNat, h_1_toNat]
          have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
          have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) + 1 < 2 ^ 32 := by decide
          omega
        -- Step 15: y_d +? 1.
        have h_add_yd_1 : (y * 2 +? (1 : u32) : RustM u32) = pure (y * 2 + 1) := by
          show (rust_primitives.ops.arith.Add.add (y * 2) (1 : u32) : RustM u32) = _
          show (if BitVec.uaddOverflow (y * 2).toBitVec (1 : u32).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (y * 2 + 1)) = _
          have h_no_ovf : BitVec.uaddOverflow (y * 2).toBitVec (1 : u32).toBitVec = false := by
            cases h_eq : BitVec.uaddOverflow (y * 2).toBitVec (1 : u32).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.addOverflow (y * 2) (1 : u32) = true := h_eq
              rw [UInt32.addOverflow_iff] at this
              rw [h_1_toNat, h_yd_toNat] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_add_yd_1]
        simp only [pure_bind]
        have h_ynew_toNat : (y * 2 + (1 : u32)).toNat = y.toNat * 2 + 1 := by
          rw [UInt32.toNat_add_of_lt]
          · rw [h_yd_toNat, h_1_toNat]
          rw [h_yd_toNat, h_1_toNat]; omega
        -- Apply IH with new state.
        have h_meas : (s_iter - (1 : u32)).toNat < s_iter.toNat := by
          rw [h_sn_toNat]; omega
        have h_s_le_11' : (s_iter - (1 : u32)).toNat ≤ 11 := by rw [h_sn_toNat]; omega
        -- y_new = 2y + 1, y2_new = (2y+1)².
        have h_ynew_alg : (y * 2 + (1 : u32)).toNat = 2 * y.toNat + 1 := by
          rw [h_ynew_toNat, Nat.mul_comm y.toNat 2]
        have h_y2new_eq_sq : ((y2 * 4 + (2 : u32) * (y * 2)) + (1 : u32)).toNat =
                              (y * 2 + (1 : u32)).toNat * (y * 2 + (1 : u32)).toNat := by
          rw [h_y2new_toNat, h_ynew_alg, h_y2_eq, nat_2y1_sq,
              show y.toNat * y.toNat * 4 = 4 * (y.toNat * y.toNat) from Nat.mul_comm _ _,
              show 2 * (y.toNat * 2) = 4 * y.toNat from by
                rw [Nat.mul_comm y.toNat 2, ← Nat.mul_assoc]]
        -- y_new³ · 8^(s-1) ≤ a_orig.
        have h_ynew_cube_le : (y * 2 + (1 : u32)).toNat * (y * 2 + (1 : u32)).toNat *
            (y * 2 + (1 : u32)).toNat * 8 ^ (s_iter - (1 : u32)).toNat ≤ a_orig := by
          rw [h_ynew_alg, h_cube_id, h_sn_toNat]
          -- (8y³ + b) · 8^(s-1) = 8y³·8^(s-1) + b·8^(s-1) = y³·8^s + b·2^s.
          rw [Nat.add_mul]
          rw [← h_y3_split]
          have h_2s_rw : (8 : Nat) ^ (s_iter.toNat - 1) =
              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
            rw [h_2s_eq]
          rw [h_2s_rw]
          rw [← h_b_alg]
          omega
        -- a_orig < (y_new+1)³ · 8^(s-1).
        have h_a_lt_succ_new : a_orig <
            ((y * 2 + (1 : u32)).toNat + 1) * ((y * 2 + (1 : u32)).toNat + 1) *
            ((y * 2 + (1 : u32)).toNat + 1) * 8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_ynew_alg, h_sn_toNat]
          -- (2y+2)³ · 8^(s-1) = 8(y+1)³ · 8^(s-1) = (y+1)³ · 8^s.
          have h_rw : (2 * y.toNat + 1 + 1) * (2 * y.toNat + 1 + 1) *
                      (2 * y.toNat + 1 + 1) * 8 ^ (s_iter.toNat - 1) =
                     (y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1) *
                       (8 * 8 ^ (s_iter.toNat - 1)) := by
            have h_2y2 : 2 * y.toNat + 1 + 1 = 2 * (y.toNat + 1) := by omega
            rw [h_2y2, nat_two_y_cube (y.toNat + 1),
                Nat.mul_comm 8 ((y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1)),
                Nat.mul_assoc ((y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1)) 8
                              (8 ^ (s_iter.toNat - 1))]
          rw [h_rw, ← h_8_split]
          exact h_a_lt_succ_cube
        -- x_new.toNat = a_orig - y_new³ · 8^(s-1).
        have h_xnew_inv : (x - (3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toNat =
                          a_orig - (y * 2 + (1 : u32)).toNat *
                                     (y * 2 + (1 : u32)).toNat *
                                     (y * 2 + (1 : u32)).toNat *
                                     8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_xnew_toNat, h_ynew_alg, h_cube_id, h_sn_toNat, Nat.add_mul,
              ← h_y3_split]
          have h_2s_rw : (8 : Nat) ^ (s_iter.toNat - 1) =
              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
            rw [h_2s_eq]
          rw [h_2s_rw, ← h_b_alg]
          omega
        exact ih (s_iter - (1 : u32)).toNat h_meas
                 (s_iter - (1 : u32))
                 (x - (3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))
                 ((y2 * 4 + (2 : u32) * (y * 2)) + (1 : u32))
                 (y * 2 + (1 : u32))
                 h_s_le_11' h_y2new_eq_sq h_ynew_cube_le h_a_lt_succ_new h_xnew_inv rfl
      · -- False branch: y_new = 2y.
        simp only [decide_eq_false h_ge, Bool.false_eq_true, if_false]
        have h_x_lt : x.toNat < ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                                2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
          rcases Nat.lt_or_ge x.toNat (((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                                       2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat) with h | h
          · exact h
          · exfalso; exact h_ge (h_ge_iff.mpr h)
        -- Apply IH with state (s_iter - 1, x, y2*4, y*2).
        have h_meas : (s_iter - (1 : u32)).toNat < s_iter.toNat := by
          rw [h_sn_toNat]; omega
        have h_s_le_11' : (s_iter - (1 : u32)).toNat ≤ 11 := by rw [h_sn_toNat]; omega
        -- y2_d = (2y)².
        have h_y2d_eq_sq : (y2 * (4 : u32)).toNat = (y * (2 : u32)).toNat * (y * (2 : u32)).toNat := by
          rw [h_y2d_alg, h_yd_alg]
          exact (nat_two_y_sq y.toNat).symm
        -- y_d³ · 8^(s-1) = 8y³ · 8^(s-1) = y³ · 8^s ≤ a_orig.
        have h_yd_cube_le : (y * (2 : u32)).toNat * (y * (2 : u32)).toNat *
            (y * (2 : u32)).toNat * 8 ^ (s_iter - (1 : u32)).toNat ≤ a_orig := by
          rw [h_yd_alg, h_sn_toNat]
          have h_rw : 2 * y.toNat * (2 * y.toNat) * (2 * y.toNat) * 8 ^ (s_iter.toNat - 1) =
                      y.toNat * y.toNat * y.toNat * (8 * 8 ^ (s_iter.toNat - 1)) := by
            rw [nat_two_y_cube,
                Nat.mul_comm 8 (y.toNat * y.toNat * y.toNat),
                Nat.mul_assoc (y.toNat * y.toNat * y.toNat) 8 (8 ^ (s_iter.toNat - 1))]
          rw [h_rw, ← h_8_split]
          exact h_y_cube_le
        -- a_orig < (2y+1)³ · 8^(s-1) (from x < b · 2^s and x = a - y³·8^s).
        have h_a_lt_succ_d : a_orig <
            ((y * (2 : u32)).toNat + 1) * ((y * (2 : u32)).toNat + 1) *
            ((y * (2 : u32)).toNat + 1) * 8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_yd_alg, h_sn_toNat]
          rw [show (2 * y.toNat + 1) * (2 * y.toNat + 1) * (2 * y.toNat + 1) *
                   8 ^ (s_iter.toNat - 1) =
                   (2 * y.toNat + 1) * (2 * y.toNat + 1) * (2 * y.toNat + 1) *
                   8 ^ (s_iter.toNat - 1) from rfl]
          rw [h_cube_id, Nat.add_mul, ← h_y3_split]
          have h_2s_rw : (8 : Nat) ^ (s_iter.toNat - 1) =
              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
            rw [h_2s_eq]
          rw [h_2s_rw, ← h_b_alg]
          omega
        -- x.toNat = a_orig - y_d³ · 8^(s-1).
        have h_x_inv_d : x.toNat = a_orig - (y * (2 : u32)).toNat *
                                              (y * (2 : u32)).toNat *
                                              (y * (2 : u32)).toNat *
                                              8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_yd_alg, h_sn_toNat]
          have h_rw : 2 * y.toNat * (2 * y.toNat) * (2 * y.toNat) * 8 ^ (s_iter.toNat - 1) =
                      y.toNat * y.toNat * y.toNat * (8 * 8 ^ (s_iter.toNat - 1)) := by
            rw [nat_two_y_cube,
                Nat.mul_comm 8 (y.toNat * y.toNat * y.toNat),
                Nat.mul_assoc (y.toNat * y.toNat * y.toNat) 8 (8 ^ (s_iter.toNat - 1))]
          rw [h_rw, ← h_8_split]
          exact h_x_eq
        exact ih (s_iter - (1 : u32)).toNat h_meas
                 (s_iter - (1 : u32))
                 x
                 (y2 * (4 : u32))
                 (y * (2 : u32))
                 h_s_le_11' h_y2d_eq_sq h_yd_cube_le h_a_lt_succ_d h_x_inv_d rfl

/-- Top-level `cbrt_u32` correctness, derived from the loop invariant
    initialised at `s_iter = 11, x = a, y2 = 0, y = 0`. -/
private theorem cbrt_u32_correct (a : u32) :
    ∃ y : u32, cbrt_u64.cbrt_u32 a = RustM.ok y ∧
      y.toNat * y.toNat * y.toNat ≤ a.toNat ∧
      a.toNat < (y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1) := by
  -- Reduce cbrt_u32 a = cbrt_u32_loop (smax+1) a 0 0 with smax = 32/3 = 10.
  unfold cbrt_u64.cbrt_u32
  -- 32 /? 3 = pure 10 (no overflow, since 3 ≠ 0).
  have h_div : ((32 : u32) /? (3 : u32) : RustM u32) = pure (10 : u32) := by
    show (rust_primitives.ops.arith.Div.div (32 : u32) (3 : u32) : RustM u32) = pure 10
    show (if (3 : u32) = 0 then (.fail .divisionByZero : RustM u32) else pure ((32 : u32) / 3)) = pure 10
    rw [if_neg (by decide : (3 : u32) ≠ 0)]
    rfl
  rw [h_div]
  simp only [pure_bind]
  -- 10 +? 1 = pure 11 (no overflow).
  have h_add : ((10 : u32) +? (1 : u32) : RustM u32) = pure (11 : u32) := by
    show (rust_primitives.ops.arith.Add.add (10 : u32) (1 : u32) : RustM u32) = pure 11
    show (if BitVec.uaddOverflow (10 : u32).toBitVec (1 : u32).toBitVec then
            (.fail .integerOverflow : RustM u32)
          else pure ((10 : u32) + 1)) = pure 11
    rw [show (BitVec.uaddOverflow (10 : u32).toBitVec (1 : u32).toBitVec) = false from by decide]
    rfl
  rw [h_add]
  simp only [pure_bind]
  -- Apply the loop invariant with y = 0, y2 = 0, x = a, s_iter = 11.
  have h_11_toNat : (11 : u32).toNat = 11 := rfl
  have h_0_toNat : (0 : u32).toNat = 0 := rfl
  have h_a_lt : a.toNat < 2 ^ 32 := a.toNat_lt
  refine cbrt_u32_loop_correct (11 : u32) a (0 : u32) (0 : u32) a.toNat h_a_lt
    ?_ ?_ ?_ ?_ ?_
  · rw [h_11_toNat]; omega
  · rw [h_0_toNat]
  · rw [h_0_toNat, h_11_toNat]
    -- 0 * 0 * 0 * 8^11 = 0 ≤ a.toNat ✓
    omega
  · rw [h_0_toNat, h_11_toNat]
    -- a.toNat < (0+1)*(0+1)*(0+1) * 8^11 = 8^11 = 2^33 > 2^32 > a.toNat ✓
    have h_8_11 : (8 : Nat) ^ 11 = 2 ^ 33 := by decide
    have h_2_33 : (2 : Nat) ^ 33 > 2 ^ 32 := by decide
    show a.toNat < (0 + 1) * (0 + 1) * (0 + 1) * 8 ^ 11
    omega
  · rw [h_0_toNat, h_11_toNat]
    -- x.toNat = a.toNat - 0 * 0 * 0 * 8^11 = a.toNat ✓
    omega

/-! ## Newton loop specs (`fixpoint_cbrt_up` / `fixpoint_cbrt_down`).

When the starting `x` is an overestimate (`x³ ≥ a`), the upward loop
exits in one step (since `xn = (a/x² + 2x)/3 ≤ x` when `a ≤ x³`).
The downward loop then descends until `xn ≥ x`, at which point
`x = floor(cbrt(a))`. -/

/-- `fixpoint_cbrt_up` when called with an overestimate `x³ ≥ a` exits
    immediately, returning `(x, xn)` where `xn ≤ x`. -/
private theorem fixpoint_cbrt_up_spec_overest (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_x_cube_ge : a.toNat ≤ x.toNat * x.toNat * x.toNat)
    (h_xn_eq : xn.toNat = (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3) :
    cbrt_u64.fixpoint_cbrt_up a x xn
      = RustM.ok (rust_primitives.hax.Tuple2.mk x xn)
    ∧ xn.toNat ≤ x.toNat := by
  -- Since x³ ≥ a, we have xn ≤ x (Newton from overestimate goes down).
  have h_xn_le_x : xn.toNat ≤ x.toNat := by
    rw [h_xn_eq]
    -- (a/x² + 2x)/3 ≤ x. Use nat_iter_cbrt_ge_self_iff in reverse: NOT (x ≤ (a/x²+2x)/3) since a < x³ ... wait.
    -- Actually, if a ≤ x³, then a/x² ≤ x (from div), so a/x² + 2x ≤ 3x, so /3 ≤ x.
    have hxx_pos : 0 < x.toNat * x.toNat := Nat.mul_pos h_x_pos h_x_pos
    -- a/(x*x) ≤ x (since a ≤ x*x*x = x*(x*x))
    have h_a_le : a.toNat ≤ x.toNat * (x.toNat * x.toNat) := by
      rw [← Nat.mul_assoc]; exact h_x_cube_ge
    have h_div_le : a.toNat / (x.toNat * x.toNat) ≤ (x.toNat * (x.toNat * x.toNat)) / (x.toNat * x.toNat) :=
      Nat.div_le_div_right h_a_le
    have h_self : x.toNat * (x.toNat * x.toNat) / (x.toNat * x.toNat) = x.toNat :=
      Nat.mul_div_cancel x.toNat hxx_pos
    have h_q_le : a.toNat / (x.toNat * x.toNat) ≤ x.toNat := by omega
    -- (q + 2x)/3 ≤ (x + 2x)/3 = x
    have h_sum_le : a.toNat / (x.toNat * x.toNat) + 2 * x.toNat ≤ 3 * x.toNat := by omega
    have h_div_le2 : (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3 ≤ (3 * x.toNat) / 3 :=
      Nat.div_le_div_right h_sum_le
    have h_simp : (3 * x.toNat) / 3 = x.toNat := by
      rw [Nat.mul_comm]; exact Nat.mul_div_cancel x.toNat (by decide)
    omega
  -- Now unfold and take the else branch.
  refine ⟨?_, h_xn_le_x⟩
  unfold cbrt_u64.fixpoint_cbrt_up
  have h_lt_eqq : (x <? xn : RustM Bool) = pure (decide (x < xn)) := rfl
  rw [h_lt_eqq]
  simp only [pure_bind]
  have h_not_lt : ¬ x < xn := by
    intro h
    have h_lt_N : x.toNat < xn.toNat := UInt64.lt_iff_toNat_lt.mp h
    omega
  rw [decide_eq_false h_not_lt]
  simp only [Bool.false_eq_true, if_false]
  rfl

/-- Reduction of `(x : u64) *? x` when `x.toNat ≤ 2^22`. -/
private theorem u64_mul_self_no_ovf (x : u64) (h : x.toNat ≤ 2 ^ 22) :
    (x *? x : RustM u64) = pure (x * x) := by
  show (rust_primitives.ops.arith.Mul.mul x x : RustM u64) = pure (x * x)
  show (if BitVec.umulOverflow x.toBitVec x.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x * x)) = pure (x * x)
  have h_no_ovf' : BitVec.umulOverflow x.toBitVec x.toBitVec = false := by
    cases h_eq : BitVec.umulOverflow x.toBitVec x.toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.mulOverflow x x = true := h_eq
      rw [UInt64.mulOverflow_iff] at this
      have h_sq_le : x.toNat * x.toNat ≤ 2^22 * 2^22 := Nat.mul_le_mul h h
      have h_pow : (2 : Nat)^22 * 2^22 = 2^44 := by rw [← Nat.pow_add]
      have h_44_64 : (2 : Nat)^44 < 2^64 := by decide
      omega
  rw [h_no_ovf']; rfl

/-- Reduction for `x *? 2` when `x.toNat ≤ 2^22`. -/
private theorem u64_mul_2_no_ovf (x : u64) (h : x.toNat ≤ 2 ^ 22) :
    (x *? (2 : u64) : RustM u64) = pure (x * 2) := by
  show (rust_primitives.ops.arith.Mul.mul x (2 : u64) : RustM u64) = pure (x * 2)
  show (if BitVec.umulOverflow x.toBitVec (2 : u64).toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x * 2)) = pure (x * 2)
  have h_no_ovf' : BitVec.umulOverflow x.toBitVec (2 : u64).toBitVec = false := by
    cases h_eq : BitVec.umulOverflow x.toBitVec (2 : u64).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.mulOverflow x (2 : u64) = true := h_eq
      rw [UInt64.mulOverflow_iff] at this
      have h2 : (2 : UInt64).toNat = 2 := rfl
      rw [h2] at this
      omega
  rw [h_no_ovf']; rfl

/-- `(2·n)³ = 8·n³`. -/
private theorem nat_two_mul_cube (n : Nat) :
    (2*n) * (2*n) * (2*n) = 8 * (n*n*n) := by
  have h1 : 2*n*(2*n) = 4*(n*n) := by
    rw [Nat.mul_assoc 2 n (2*n)]
    have h_in : n * (2*n) = 2 * (n*n) := by
      rw [← Nat.mul_assoc n 2 n, Nat.mul_comm n 2, Nat.mul_assoc]
    rw [h_in, ← Nat.mul_assoc]
  rw [h1, Nat.mul_assoc 4 (n*n) (2*n)]
  have h2 : n*n*(2*n) = 2*(n*n*n) := by
    rw [← Nat.mul_assoc (n*n) 2 n, Nat.mul_comm (n*n) 2, Nat.mul_assoc]
  rw [h2, ← Nat.mul_assoc]

/-- Bound: `a < (xn+1)³ → a/(xn*xn) ≤ 8*xn` for `xn ≥ 1`. -/
private theorem nat_a_div_xnxn_le_8xn (a xn : Nat) (hxn : 0 < xn)
    (h_a_lt : a < (xn + 1) * (xn + 1) * (xn + 1)) :
    a / (xn * xn) ≤ 8 * xn := by
  -- (xn+1) ≤ 2*xn since xn ≥ 1, so (xn+1)³ ≤ (2*xn)³ = 8*xn³.
  have h_xn1_le : xn + 1 ≤ 2 * xn := by omega
  have h_cube_le : (xn + 1) * (xn + 1) * (xn + 1) ≤ (2 * xn) * (2 * xn) * (2 * xn) :=
    Nat.mul_le_mul (Nat.mul_le_mul h_xn1_le h_xn1_le) h_xn1_le
  have h_2xn_cube : (2 * xn) * (2 * xn) * (2 * xn) = 8 * (xn * xn * xn) := nat_two_mul_cube xn
  have h_a_lt' : a < 8 * (xn * xn * xn) := by omega
  -- a < 8*xn³ = (8*xn) * (xn*xn). So a/(xn*xn) < 8*xn.
  have h_factor : 8 * (xn * xn * xn) = (8 * xn) * (xn * xn) := by
    rw [Nat.mul_assoc 8 xn (xn*xn)]
    have h_eq : xn * (xn * xn) = (xn * xn) * xn := Nat.mul_comm _ _
    rw [h_eq, ← Nat.mul_assoc]
  have hxx_pos : 0 < xn * xn := Nat.mul_pos hxn hxn
  rw [h_factor] at h_a_lt'
  have h_div_lt : a / (xn * xn) < 8 * xn :=
    (Nat.div_lt_iff_lt_mul hxx_pos).mpr h_a_lt'
  omega

/-- `fixpoint_cbrt_down` loop spec: descends from a state with
    `a < (x+1)³` invariant to `r = floor(cbrt(a))`. Termination by
    strong induction on `x.toNat`. -/
private theorem fixpoint_cbrt_down_spec (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_x_ub : a.toNat < (x.toNat + 1) * (x.toNat + 1) * (x.toNat + 1))
    (h_xn_eq : xn.toNat = (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3)
    (h_a_pos : 1 ≤ a.toNat)
    (h_x_le : x.toNat ≤ 2 ^ 22) :
    ∃ r : u64, cbrt_u64.fixpoint_cbrt_down a x xn = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  induction hk : x.toNat using Nat.strongRecOn generalizing x xn with
  | _ k ih =>
    subst hk
    unfold cbrt_u64.fixpoint_cbrt_down
    have h_gt_eqq : (x >? xn : RustM Bool) = pure (decide (x > xn)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hgt : x > xn
    · -- Recursive case: x > xn, descend.
      simp only [decide_eq_true hgt, if_true]
      have h_xn_lt_x : xn.toNat < x.toNat := UInt64.lt_iff_toNat_lt.mp hgt
      -- xn ≥ 1: since x > xn and the Newton step from x gives xn, with a ≥ 1.
      -- Specifically: if a ≥ 1 and x ≥ 1, then (a/x² + 2x)/3 ≥ 1 when 2x ≥ 3 (x ≥ 2).
      -- If x = 1: xn = (a + 2)/3. For a ≥ 1, xn ≥ 1.
      have h_xn_pos : 0 < xn.toNat := by
        rw [h_xn_eq]
        rcases Nat.lt_or_ge x.toNat 2 with h_x_lt | h_x_ge
        · -- x = 1: xn = (a/1 + 2)/3 = (a+2)/3 ≥ 1 since a ≥ 1.
          have hx1 : x.toNat = 1 := by omega
          rw [hx1]
          have h_one : (1 : Nat) * 1 = 1 := rfl
          rw [h_one, Nat.div_one]
          have h_sum_ge : 3 ≤ a.toNat + 2 * 1 := by omega
          have h_div_le : (3 : Nat) / 3 ≤ (a.toNat + 2 * 1) / 3 := Nat.div_le_div_right h_sum_ge
          have h_three : (3 : Nat) / 3 = 1 := by decide
          omega
        · -- x ≥ 2: 2x ≥ 4, so sum ≥ 4, /3 ≥ 1.
          have h_2x_ge : 2 * x.toNat ≥ 4 := by omega
          have h_div_nn : 0 ≤ a.toNat / (x.toNat * x.toNat) := Nat.zero_le _
          have h_sum_ge : 4 ≤ a.toNat / (x.toNat * x.toNat) + 2 * x.toNat := by omega
          have h_div_le : (4 : Nat) / 3 ≤ (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3 :=
            Nat.div_le_div_right h_sum_ge
          have h_four : (4 : Nat) / 3 = 1 := by decide
          omega
      have h_xn_le_22 : xn.toNat ≤ 2 ^ 22 := by omega
      -- xn *? xn
      rw [u64_mul_self_no_ovf xn h_xn_le_22]
      simp only [pure_bind]
      have h_xnxn_toNat : (xn * xn).toNat = xn.toNat * xn.toNat := by
        apply UInt64.toNat_mul_of_lt
        have h_sq_le : xn.toNat * xn.toNat ≤ 2^22 * 2^22 := Nat.mul_le_mul h_xn_le_22 h_xn_le_22
        have h_pow : (2 : Nat)^22 * 2^22 = 2^44 := by rw [← Nat.pow_add]
        have h_44_64 : (2 : Nat)^44 < 2^64 := by decide
        omega
      have h_xn_xn_ne : xn * xn ≠ 0 := by
        intro hcon
        have h0 : (xn * xn).toNat = 0 := by rw [hcon]; rfl
        rw [h_xnxn_toNat] at h0
        have h_n0 : xn.toNat = 0 := by
          rcases Nat.eq_zero_or_pos xn.toNat with h | h
          · exact h
          · exfalso; have := Nat.mul_pos h h; omega
        omega
      have h_div_a : (a /? (xn * xn) : RustM u64) = pure (a / (xn * xn)) := by
        show (rust_primitives.ops.arith.Div.div a (xn * xn) : RustM u64) = pure (a / (xn * xn))
        show (if (xn * xn) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
        rw [if_neg h_xn_xn_ne]
      rw [h_div_a]
      simp only [pure_bind]
      have h_a_div_toNat : (a / (xn * xn)).toNat = a.toNat / (xn.toNat * xn.toNat) := by
        rw [UInt64.toNat_div, h_xnxn_toNat]
      rw [u64_mul_2_no_ovf xn h_xn_le_22]
      simp only [pure_bind]
      have h_xn2_toNat : (xn * (2 : u64)).toNat = xn.toNat * 2 := by
        apply UInt64.toNat_mul_of_lt
        have h2 : (2 : UInt64).toNat = 2 := rfl
        rw [h2]
        have h_xn_2 : xn.toNat * 2 ≤ 2^22 * 2 := Nat.mul_le_mul_right 2 h_xn_le_22
        have h_pow : (2 : Nat)^22 * 2 < 2^64 := by decide
        omega
      -- Newton step bound: a < (xn+1)³.
      have h_iter_lb : a.toNat < (xn.toNat + 1) * (xn.toNat + 1) * (xn.toNat + 1) := by
        have h_lb := nat_cubic_newton_lb a.toNat x.toNat h_x_pos
        rw [← h_xn_eq] at h_lb
        exact h_lb
      -- a/(xn*xn) ≤ 8*xn (from the helper).
      have h_a_div_le : a.toNat / (xn.toNat * xn.toNat) ≤ 8 * xn.toNat :=
        nat_a_div_xnxn_le_8xn a.toNat xn.toNat h_xn_pos h_iter_lb
      have h_no_ovf : a.toNat / (xn.toNat * xn.toNat) + xn.toNat * 2 < 2 ^ 64 := by
        -- Sum ≤ 8*xn + 2*xn = 10*xn ≤ 10*2^22 < 2^64
        have h_pow_lt : 10 * (2 : Nat)^22 < 2^64 := by decide
        have h_10xn : 10 * xn.toNat ≤ 10 * 2^22 := Nat.mul_le_mul_left 10 h_xn_le_22
        omega
      have h_add : ((a / (xn * xn)) +? (xn * 2) : RustM u64) =
                   pure ((a / (xn * xn)) + (xn * 2)) := by
        show (rust_primitives.ops.arith.Add.add (a / (xn * xn)) (xn * 2) : RustM u64) = _
        show (if BitVec.uaddOverflow (a / (xn * xn)).toBitVec (xn * 2).toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure ((a / (xn * xn)) + (xn * 2))) = _
        have h_no_ovf' : BitVec.uaddOverflow (a / (xn * xn)).toBitVec (xn * 2).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (a / (xn * xn)).toBitVec (xn * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow (a / (xn * xn)) (xn * 2) = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            rw [h_a_div_toNat, h_xn2_toNat] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      have h_sumN : ((a / (xn * xn)) + (xn * 2)).toNat
                    = a.toNat / (xn.toNat * xn.toNat) + xn.toNat * 2 := by
        rw [UInt64.toNat_add_of_lt]
        · rw [h_a_div_toNat, h_xn2_toNat]
        rw [h_a_div_toNat, h_xn2_toNat]; exact h_no_ovf
      have h_div3 : ((a / (xn * xn) + xn * 2) /? (3 : u64) : RustM u64) =
                    pure ((a / (xn * xn) + xn * 2) / 3) := by
        show (rust_primitives.ops.arith.Div.div ((a / (xn * xn)) + (xn * 2)) (3 : u64) : RustM u64) = _
        show (if (3 : u64) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
        rw [if_neg (by decide : (3 : u64) ≠ 0)]
      rw [h_div3]
      simp only [pure_bind]
      have h_newxn_N : ((a / (xn * xn) + xn * 2) / 3).toNat
                      = (a.toNat / (xn.toNat * xn.toNat) + xn.toNat * 2) / 3 := by
        rw [UInt64.toNat_div, h_sumN]
        have h3 : (3 : UInt64).toNat = 3 := rfl; rw [h3]
      -- The new xn = (a/(xn*xn) + xn*2)/3. The spec uses (a/(xn²) + 2*xn)/3.
      have h_newxn_N' : ((a / (xn * xn) + xn * 2) / 3).toNat
                      = (a.toNat / (xn.toNat * xn.toNat) + 2 * xn.toNat) / 3 := by
        rw [h_newxn_N, Nat.mul_comm xn.toNat 2]
      -- Apply IH with x' = xn, xn' = new_xn.
      -- Need: 0 < xn.toNat ✓; a < (xn+1)³ ✓; new_xn = Newton(xn); a ≥ 1 ✓; xn ≤ 2^22 ✓.
      -- Measure: xn.toNat < x.toNat ✓.
      obtain ⟨r, hr_eq, hr_lb, hr_ub⟩ :=
        ih xn.toNat h_xn_lt_x xn ((a / (xn * xn) + xn * 2) / 3)
          h_xn_pos h_iter_lb h_newxn_N' h_xn_le_22 rfl
      exact ⟨r, hr_eq, hr_lb, hr_ub⟩
    · -- Base case: x ≤ xn, exit with x.
      simp only [decide_eq_false hgt, Bool.false_eq_true, if_false]
      refine ⟨x, rfl, ?_, h_x_ub⟩
      have h_x_le_xn : x.toNat ≤ xn.toNat := by
        have h_not : ¬ x.toNat > xn.toNat := fun h => hgt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have h_x_le_iter : x.toNat ≤ (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3 := by
        rw [← h_xn_eq]; exact h_x_le_xn
      exact (nat_iter_cbrt_ge_self_iff a.toNat x.toNat h_x_pos).mp h_x_le_iter

/-! ## Newton fixpoint correctness for `cbrt_guess_u64` and `fixpoint_cbrt`.

For inputs `a > 2^32`, the function computes:
  * `g = cbrt_guess_u64 a` — a power-of-two `g` with `g ≥ cbrt(a)` and `g ≤ 2^22`.
  * `fixpoint_cbrt a g` — converges to `floor(cbrt(a))` via the Newton recurrence
    `(a/x² + 2x)/3`.

The cubic-Newton proof shape mirrors `sqrt_loop_up_spec` /
`sqrt_loop_down_spec` in `proof_patterns/sqrt_u64_modified`, but with
the cubic Newton step in place of the quadratic Babylonian step. The
core algebraic identity, in the spirit of AM-GM for cubes, is:

   For `0 < x`, `a < ((a/x² + 2x)/3 + 1)³`  (`nat_cubic_newton_lb`)

derived from the 3-variable AM-GM `(q + 2x)³ ≥ 27qx²`
(`nat_cubic_amgm`), in turn derived from the 2-variable AM-GM
`q² + x² ≥ 2qx` (`nat_sq_sum_ge_2_mul`) via multiplying by `q` and `x`
respectively and chaining linear combinations through `omega`.

All three helpers below are *fully proven*; their composition closes
the Newton arm of the master theorem. -/

/-- `cbrt_guess_u64` correctness. Returns `g > 0` with `g ≤ 2^22` such
    that `cbrt(a) ≤ g` (i.e., `a ≤ g³`). Proven by composing
    `log2_floor_rec_correct` + `pow2_loop_correct` through the monadic
    chain `log2_floor_rec → +? 3 → /? 3 → pow2_loop`. -/
private theorem cbrt_guess_u64_correct (a : u64) (h_a_ge : a.toNat ≥ 2 ^ 32) :
    ∃ g : u64, cbrt_u64.cbrt_guess_u64 a = RustM.ok g ∧
      0 < g.toNat ∧
      g.toNat ≤ 2 ^ 22 ∧
      a.toNat ≤ g.toNat * g.toNat * g.toNat := by
  unfold cbrt_u64.cbrt_guess_u64
  have h_a_pos : 0 < a.toNat := by omega
  have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
  have h_log2_le : Nat.log2 a.toNat ≤ 63 := nat_log2_le_63 a.toNat h_a_pos h_a_lt
  have h_log2_ge : Nat.log2 a.toNat ≥ 32 := by
    rcases Nat.lt_or_ge (Nat.log2 a.toNat) 32 with h | h
    · exfalso
      have h_x_lt : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) := nat_lt_pow_succ_log2 a.toNat h_a_pos
      have h_pow_le : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact h
  -- Step 1: reduce log2_floor_rec a 0.
  have h_log2_eq : cbrt_u64.log2_floor_rec a (0 : u32) =
                   RustM.ok (UInt32.ofNat (Nat.log2 a.toNat)) := by
    have h := log2_floor_rec_correct a (0 : u32) (by
      show (0 : UInt32).toNat + Nat.log2 a.toNat < 2 ^ 32
      have h0 : (0 : UInt32).toNat = 0 := rfl
      rw [h0]; omega)
    rw [h]
    have h0 : (0 : UInt32).toNat = 0 := rfl
    rw [h0, Nat.zero_add]
  rw [h_log2_eq]
  simp only [RustM_ok_bind]
  -- Step 2: reduce `(UInt32.ofNat (log2 a)) +? 3`.
  have h_log2_toNat : (UInt32.ofNat (Nat.log2 a.toNat)).toNat = Nat.log2 a.toNat :=
    UInt32.toNat_ofNat_of_lt' (by omega : Nat.log2 a.toNat < 2 ^ 32)
  have h_add3 : ((UInt32.ofNat (Nat.log2 a.toNat)) +? (3 : u32) : RustM u32) =
                pure (UInt32.ofNat (Nat.log2 a.toNat) + 3) := by
    show (rust_primitives.ops.arith.Add.add (UInt32.ofNat (Nat.log2 a.toNat)) (3 : u32) : RustM u32) =
         pure (UInt32.ofNat (Nat.log2 a.toNat) + 3)
    show (if BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (3 : u32).toBitVec then
            (.fail .integerOverflow : RustM u32)
          else pure (UInt32.ofNat (Nat.log2 a.toNat) + 3)) =
         pure (UInt32.ofNat (Nat.log2 a.toNat) + 3)
    have h_no_ovf : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (3 : u32).toBitVec = false := by
      cases h_eq : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (3 : u32).toBitVec with
      | false => rfl
      | true =>
        exfalso
        have : UInt32.addOverflow (UInt32.ofNat (Nat.log2 a.toNat)) (3 : u32) = true := h_eq
        rw [UInt32.addOverflow_iff] at this
        rw [h_log2_toNat, show (3 : UInt32).toNat = 3 from rfl] at this
        omega
    rw [h_no_ovf]; rfl
  rw [h_add3]
  simp only [pure_bind]
  have h_log2p3_toNat : (UInt32.ofNat (Nat.log2 a.toNat) + 3).toNat = Nat.log2 a.toNat + 3 := by
    have h_no_ovf : (UInt32.ofNat (Nat.log2 a.toNat)).toNat + (3 : UInt32).toNat < 2 ^ 32 := by
      rw [h_log2_toNat, show (3 : UInt32).toNat = 3 from rfl]; omega
    rw [UInt32.toNat_add_of_lt h_no_ovf, h_log2_toNat, show (3 : UInt32).toNat = 3 from rfl]
  -- Step 3: reduce `(hi+3) /? 3`.
  have h_div3 : ((UInt32.ofNat (Nat.log2 a.toNat) + 3) /? (3 : u32) : RustM u32) =
                pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3) := by
    show (rust_primitives.ops.arith.Div.div (UInt32.ofNat (Nat.log2 a.toNat) + 3) (3 : u32) : RustM u32) =
         pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3)
    show (if (3 : u32) = 0 then (.fail .divisionByZero : RustM u32) else pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3)) =
         pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3)
    rw [if_neg (by decide : (3 : u32) ≠ 0)]
  rw [h_div3]
  simp only [pure_bind]
  have h_k_toNat : ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat
                   = (Nat.log2 a.toNat + 3) / 3 := by
    rw [UInt32.toNat_div, h_log2p3_toNat, show (3 : UInt32).toNat = 3 from rfl]
  have h_k_ge_11 : 11 ≤ (Nat.log2 a.toNat + 3) / 3 := by
    have h_div_ge : (35 : Nat) / 3 ≤ (Nat.log2 a.toNat + 3) / 3 :=
      Nat.div_le_div_right (by omega)
    have h35 : (35 : Nat) / 3 = 11 := by decide
    omega
  have h_k_le_22 : (Nat.log2 a.toNat + 3) / 3 ≤ 22 := by
    have h_le : Nat.log2 a.toNat + 3 ≤ 66 := by omega
    have h_div_le : (Nat.log2 a.toNat + 3) / 3 ≤ 66 / 3 :=
      Nat.div_le_div_right h_le
    have h66 : (66 : Nat) / 3 = 22 := by decide
    omega
  -- Step 4: apply pow2_loop_correct with k, i = 0, g = 1.
  have h_1_toNat : (1 : u64).toNat = 1 := rfl
  have h_0_toNat : (0 : u32).toNat = 0 := rfl
  have h_no_ovf : (1 : u64).toNat * 2 ^ (((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat - (0 : u32).toNat) < 2 ^ 64 := by
    rw [h_1_toNat, h_0_toNat, h_k_toNat, Nat.sub_zero, Nat.one_mul]
    have h_pow_le : (2 : Nat) ^ ((Nat.log2 a.toNat + 3) / 3) ≤ 2 ^ 22 :=
      Nat.pow_le_pow_right (by decide) h_k_le_22
    have h_2_22 : (2 : Nat) ^ 22 < 2 ^ 64 := by decide
    omega
  have h_k_le_63 : ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat ≤ 63 := by
    rw [h_k_toNat]; omega
  have h_0_le_k : (0 : u32).toNat ≤ ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat := by
    rw [h_0_toNat]; omega
  obtain ⟨g, hg_eq, hg_toNat⟩ :=
    pow2_loop_correct ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3) (0 : u32) (1 : u64)
      h_0_le_k h_k_le_63 h_no_ovf
  have h_g_toNat_eq : g.toNat = 2 ^ ((Nat.log2 a.toNat + 3) / 3) := by
    rw [hg_toNat, h_1_toNat, h_0_toNat, Nat.sub_zero, Nat.one_mul, h_k_toNat]
  refine ⟨g, hg_eq, ?_, ?_, ?_⟩
  · -- 0 < g
    rw [h_g_toNat_eq]
    exact Nat.pow_pos (by decide : 0 < 2)
  · -- g ≤ 2^22
    rw [h_g_toNat_eq]
    exact Nat.pow_le_pow_right (by decide) h_k_le_22
  · -- a ≤ g³
    rw [h_g_toNat_eq]
    have h_3k_ge : 3 * ((Nat.log2 a.toNat + 3) / 3) ≥ Nat.log2 a.toNat + 1 := by
      have h_div_mod := Nat.div_add_mod (Nat.log2 a.toNat + 3) 3
      have h_mod_lt : (Nat.log2 a.toNat + 3) % 3 < 3 := Nat.mod_lt _ (by decide)
      omega
    have h_pow_log_a : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) := nat_lt_pow_succ_log2 a.toNat h_a_pos
    have h_pow_chain : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ (3 * ((Nat.log2 a.toNat + 3) / 3)) :=
      Nat.pow_le_pow_right (by decide) h_3k_ge
    have h_pow_cube : 2 ^ (3 * ((Nat.log2 a.toNat + 3) / 3)) =
      2 ^ ((Nat.log2 a.toNat + 3) / 3) * 2 ^ ((Nat.log2 a.toNat + 3) / 3) *
      2 ^ ((Nat.log2 a.toNat + 3) / 3) := by
      rw [show 3 * ((Nat.log2 a.toNat + 3) / 3) =
              (Nat.log2 a.toNat + 3) / 3 + (Nat.log2 a.toNat + 3) / 3 + (Nat.log2 a.toNat + 3) / 3
              from by omega,
          Nat.pow_add, Nat.pow_add]
    rw [h_pow_cube] at h_pow_chain
    omega

/-! ## Master postcondition

The Rust source `cbrt : u64 → u64` returns the truncated integer cube
root: the largest `r : u64` with `r³ ≤ x`. Its contract is captured by
two universal bounds on the result:

  * **Lower bound** — `r³ ≤ x`        (P1: "r is a cube-root candidate"),
  * **Upper bound** — `x < (r+1)³`    (P2: "r is the *greatest* such").

Both bounds are stated at `Nat`-level so that the "modulo u64 overflow"
caveat from the Rust property test disappears — when
`r = cbrt(2^64 − 1) = 2_642_245`, the cube `(r+1)³ ≈ 1.85 × 10^19`
exceeds `2^64`, so the genuine `Nat` inequality
`x.toNat < (r+1)³` still holds (since `x.toNat < 2^64`).

The function is total: no precondition is needed. For every `u64` input
the result fits in `u64` (`cbrt(2^64 − 1) = 2_642_245 < 2^32`), and the
intermediate partial operators (`*?`/`+?`/`/?`/`<<<?`/`>>>?`) inside
the helpers are discharged by branch-specific invariants:

  * `a < 8`        — early return `0` or `1`, no arithmetic.
  * `a ≤ u32::MAX` — Hacker's-Delight `icbrt2` running entirely in `u32`,
                     with the bit-width bound `s ≤ 10` keeping every shift
                     and add in range.
  * `a > u32::MAX` — `cbrt_guess_u64` produces `g ≤ 2^22 < 2^32`, so the
                     Newton recurrence `(a/(x*x) + 2*x)/3` keeps `x ≤ 2^32`
                     invariantly; therefore `x*x < 2^64`, `a/(x*x) > 0`
                     (so the divisor in the *next* step is positive),
                     `2*x < 2^33`, and `a/(x*x) + 2*x < 2^64`.

This master theorem bundles both bounds with the function's totality
(`= RustM.ok r`); the individual contract clauses below project out of
this lemma. -/
theorem cbrt_postcondition (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ x.toNat ∧
      x.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  unfold cbrt_u64.cbrt
  dsimp only
  rw [show (x <? (8 : u64) : RustM Bool) = pure (decide (x < 8)) from rfl]
  simp only [pure_bind]
  by_cases h_lt_8 : x < 8
  · -- Small-case arm: x.toNat ∈ {0..7}.
    rw [decide_eq_true h_lt_8]
    simp only [if_true]
    rw [show (x >? (0 : u64) : RustM Bool) = pure (decide (x > 0)) from rfl]
    simp only [pure_bind]
    have hx_lt_8 : x.toNat < 8 := UInt64.lt_iff_toNat_lt.mp h_lt_8
    by_cases h_pos : x > 0
    · rw [decide_eq_true h_pos]
      simp only [if_true]
      have hx_pos : 0 < x.toNat := UInt64.lt_iff_toNat_lt.mp h_pos
      refine ⟨1, rfl, ?_, ?_⟩
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]; omega
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]; omega
    · rw [decide_eq_false h_pos]
      simp only [Bool.false_eq_true, if_false]
      have hx_zero : x.toNat = 0 := by
        have h_not_pos : ¬ (0 < x.toNat) := fun h => h_pos (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      refine ⟨0, rfl, ?_, ?_⟩
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0]; omega
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0, hx_zero]; decide
  · -- Big-case arm (x ≥ 8): icbrt2 or Newton fixpoint.
    rw [decide_eq_false h_lt_8]
    simp only [Bool.false_eq_true, if_false]
    rw [show (x <=? (4294967295 : u64) : RustM Bool) = pure (decide (x ≤ 4294967295)) from rfl]
    simp only [pure_bind]
    have hx_ge_8 : x.toNat ≥ 8 := by
      have h_not : ¬ x.toNat < 8 := fun h => h_lt_8 (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    by_cases h_le_u32 : x ≤ 4294967295
    · -- u32 branch: cbrt_u32 on (x as u32) then cast back.
      rw [decide_eq_true h_le_u32]
      simp only [if_true]
      -- Reduce `rust_primitives.hax.cast_op x : RustM u32` to `pure x.toUInt32`.
      have h_cast1 : (rust_primitives.hax.cast_op x : RustM u32) = pure x.toUInt32 := rfl
      rw [h_cast1]
      simp only [pure_bind]
      have hx_le_2_32 : x.toNat ≤ 2 ^ 32 - 1 := by
        have h := UInt64.le_iff_toNat_le.mp h_le_u32
        have h_simp : (4294967295 : u64).toNat = 4294967295 := rfl
        rw [h_simp] at h
        omega
      -- x.toUInt32.toNat = x.toNat since x fits in u32.
      have h_toU32_toNat : x.toUInt32.toNat = x.toNat := by
        rw [UInt64.toNat_toUInt32]
        exact Nat.mod_eq_of_lt (by omega)
      -- Apply cbrt_u32_correct.
      obtain ⟨y32, hy32_eq, hy32_lb, hy32_ub⟩ := cbrt_u32_correct x.toUInt32
      rw [hy32_eq]
      simp only [RustM_ok_bind]
      -- Reduce `rust_primitives.hax.cast_op y32 : RustM u64` to `pure y32.toUInt64`.
      have h_cast2 : (rust_primitives.hax.cast_op y32 : RustM u64) = pure y32.toUInt64 := rfl
      rw [h_cast2]
      refine ⟨y32.toUInt64, rfl, ?_, ?_⟩
      · -- y32.toUInt64.toNat³ ≤ x.toNat. Since y32.toNat³ ≤ x.toNat (via h_toU32_toNat)
        -- and y32.toUInt64.toNat = y32.toNat.
        have h_eq : y32.toUInt64.toNat = y32.toNat := UInt32.toNat_toUInt64 y32
        rw [h_eq]
        rw [h_toU32_toNat] at hy32_lb
        exact hy32_lb
      · -- x.toNat < (y32.toUInt64.toNat + 1)³.
        have h_eq : y32.toUInt64.toNat = y32.toNat := UInt32.toNat_toUInt64 y32
        rw [h_eq]
        rw [h_toU32_toNat] at hy32_ub
        exact hy32_ub
    · -- Newton branch: cbrt_guess_u64 then fixpoint_cbrt.
      rw [decide_eq_false h_le_u32]
      simp only [Bool.false_eq_true, if_false]
      -- We have x > 2^32 - 1, so x.toNat ≥ 2^32.
      have hx_ge_2_32 : x.toNat ≥ 2 ^ 32 := by
        have h_not : ¬ x ≤ 4294967295 := h_le_u32
        have h_iff : ¬ x.toNat ≤ (4294967295 : u64).toNat := by
          intro hcon
          exact h_not (UInt64.le_iff_toNat_le.mpr hcon)
        have h_simp : (4294967295 : u64).toNat = 4294967295 := rfl
        rw [h_simp] at h_iff
        omega
      obtain ⟨g, hg_eq, hg_pos, hg_le, hg_cube_ge⟩ := cbrt_guess_u64_correct x hx_ge_2_32
      rw [hg_eq]
      simp only [RustM_ok_bind]
      -- Unfold fixpoint_cbrt.
      unfold cbrt_u64.fixpoint_cbrt
      -- Reduce `g *? g` to `pure (g * g)`. Since g.toNat ≤ 2^22, g*g ≤ 2^44 < 2^64.
      have h_g_sq_lt : g.toNat * g.toNat < 2 ^ 64 := by
        have h_g_sq_le : g.toNat * g.toNat ≤ 2 ^ 22 * 2 ^ 22 :=
          Nat.mul_le_mul hg_le hg_le
        have h_pow_add : (2 : Nat) ^ 22 * 2 ^ 22 = 2 ^ 44 := by
          rw [← Nat.pow_add]
        have h_2_44 : (2 : Nat) ^ 44 < 2 ^ 64 := by decide
        omega
      have h_mul_gg : (g *? g : RustM u64) = pure (g * g) := by
        show (rust_primitives.ops.arith.Mul.mul g g : RustM u64) = pure (g * g)
        show (if BitVec.umulOverflow g.toBitVec g.toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure (g * g)) = pure (g * g)
        have h_no_ovf' : BitVec.umulOverflow g.toBitVec g.toBitVec = false := by
          cases h_eq : BitVec.umulOverflow g.toBitVec g.toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.mulOverflow g g = true := h_eq
            rw [UInt64.mulOverflow_iff] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_mul_gg]
      simp only [pure_bind]
      have h_gg_toNat : (g * g).toNat = g.toNat * g.toNat := by
        apply UInt64.toNat_mul_of_lt
        exact h_g_sq_lt
      -- g * g ≠ 0 since g > 0.
      have h_gg_ne : g * g ≠ 0 := by
        intro hcon
        have h0 : (g * g).toNat = 0 := by rw [hcon]; rfl
        rw [h_gg_toNat] at h0
        have : g.toNat = 0 := by
          rcases Nat.eq_zero_or_pos g.toNat with h | h
          · exact h
          · exfalso; have := Nat.mul_pos h h; omega
        omega
      -- x /? (g*g)
      have h_div_x : (x /? (g * g) : RustM u64) = pure (x / (g * g)) := by
        show (rust_primitives.ops.arith.Div.div x (g * g) : RustM u64) = pure (x / (g * g))
        show (if (g * g) = 0 then (.fail .divisionByZero : RustM u64) else pure (x / (g * g))) =
             pure (x / (g * g))
        rw [if_neg h_gg_ne]
      rw [h_div_x]
      simp only [pure_bind]
      have h_xggN : (x / (g * g)).toNat = x.toNat / (g.toNat * g.toNat) := by
        rw [UInt64.toNat_div, h_gg_toNat]
      -- g *? 2
      rw [u64_mul_2_no_ovf g hg_le]
      simp only [pure_bind]
      have h_g2N : (g * (2 : u64)).toNat = g.toNat * 2 := by
        apply UInt64.toNat_mul_of_lt
        have h2 : (2 : UInt64).toNat = 2 := rfl
        rw [h2]
        have h_22 : g.toNat ≤ 2^22 := hg_le
        have h_2_22 : g.toNat * 2 ≤ 2^22 * 2 := Nat.mul_le_mul_right 2 h_22
        have h_pow : (2 : Nat)^22 * 2 < 2^64 := by decide
        omega
      -- (x / (g*g)) +? (g*2)
      -- We have x.toNat < 2^64 and g.toNat * g.toNat ≥ 1, so x / (g*g) ≤ x < 2^64.
      -- Specifically: g ≤ 2^22 so g*g ≤ 2^44. x.toNat < 2^64.
      -- x/(g*g) + g*2 ≤ x + 2^23. Could overflow if x is close to 2^64.
      -- Tighter: a ≤ g³ (from cbrt_guess_u64_correct), so x/(g*g) ≤ x/(g*g) ≤ g (from a ≤ g³).
      have h_xgg_le_g : x.toNat / (g.toNat * g.toNat) ≤ g.toNat := by
        have h_x_le : x.toNat ≤ g.toNat * g.toNat * g.toNat := hg_cube_ge
        have h_x_le2 : x.toNat ≤ g.toNat * (g.toNat * g.toNat) := by
          rw [Nat.mul_assoc] at h_x_le; exact h_x_le
        have h_gg_pos : 0 < g.toNat * g.toNat := Nat.mul_pos hg_pos hg_pos
        have h_div_le : x.toNat / (g.toNat * g.toNat) ≤ (g.toNat * (g.toNat * g.toNat)) / (g.toNat * g.toNat) :=
          Nat.div_le_div_right h_x_le2
        have h_self : g.toNat * (g.toNat * g.toNat) / (g.toNat * g.toNat) = g.toNat :=
          Nat.mul_div_cancel g.toNat h_gg_pos
        omega
      have h_g_2_22 : g.toNat * 2 ≤ 2 ^ 23 := by
        have h_g_le_22 : g.toNat ≤ 2^22 := hg_le
        have h_pow_eq : (2 : Nat) ^ 22 * 2 = 2 ^ 23 := by decide
        have : g.toNat * 2 ≤ 2 ^ 22 * 2 := Nat.mul_le_mul_right 2 h_g_le_22
        omega
      have h_add_no_ovf : x.toNat / (g.toNat * g.toNat) + g.toNat * 2 < 2 ^ 64 := by
        -- x.toNat / (g*g) ≤ g (from h_xgg_le_g), so sum ≤ g + g*2 = 3g ≤ 3*2^22 < 2^64.
        have h_3g : 3 * g.toNat ≤ 3 * 2^22 := Nat.mul_le_mul_left 3 hg_le
        have h_pow_lt : 3 * (2 : Nat)^22 < 2^64 := by decide
        omega
      have h_add : ((x / (g * g)) +? (g * 2) : RustM u64) = pure ((x / (g * g)) + (g * 2)) := by
        show (rust_primitives.ops.arith.Add.add (x / (g * g)) (g * 2) : RustM u64) = _
        show (if BitVec.uaddOverflow (x / (g * g)).toBitVec (g * 2).toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure ((x / (g * g)) + (g * 2))) = _
        have h_no_ovf' : BitVec.uaddOverflow (x / (g * g)).toBitVec (g * 2).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (x / (g * g)).toBitVec (g * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow (x / (g * g)) (g * 2) = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            rw [h_xggN, h_g2N] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      have h_sumN : ((x / (g * g)) + (g * 2)).toNat = x.toNat / (g.toNat * g.toNat) + g.toNat * 2 := by
        rw [UInt64.toNat_add_of_lt]; · rw [h_xggN, h_g2N]
        rw [h_xggN, h_g2N]; exact h_add_no_ovf
      -- (...) /? 3
      have h_div3 : ((x / (g * g) + g * 2) /? (3 : u64) : RustM u64) =
                    pure ((x / (g * g) + g * 2) / 3) := by
        show (rust_primitives.ops.arith.Div.div ((x / (g * g)) + (g * 2)) (3 : u64) : RustM u64) = _
        show (if (3 : u64) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
        rw [if_neg (by decide : (3 : u64) ≠ 0)]
      rw [h_div3]
      simp only [pure_bind]
      -- xn0 has toNat (x.toNat / (g.toNat * g.toNat) + g.toNat * 2) / 3
      have h_xn0N : ((x / (g * g) + g * 2) / 3).toNat
                    = (x.toNat / (g.toNat * g.toNat) + g.toNat * 2) / 3 := by
        rw [UInt64.toNat_div, h_sumN]
        have h3 : (3 : UInt64).toNat = 3 := rfl
        rw [h3]
      -- Now we need to align: spec uses (a/(x*x) + 2*x)/3, code is (x/(g*g) + g*2)/3.
      -- These are equal since g*2 = 2*g (in Nat).
      have h_xn0N' : ((x / (g * g) + g * 2) / 3).toNat
                    = (x.toNat / (g.toNat * g.toNat) + 2 * g.toNat) / 3 := by
        rw [h_xn0N, Nat.mul_comm g.toNat 2]
      -- Apply fixpoint_cbrt_up_spec_overest
      have hx_pos : 0 < x.toNat := by omega
      obtain ⟨h_up_eq, h_xn_le_g⟩ :=
        fixpoint_cbrt_up_spec_overest x g ((x / (g * g) + g * 2) / 3) hg_pos hg_cube_ge h_xn0N'
      rw [h_up_eq]
      simp only [RustM_ok_bind]
      -- Now apply fixpoint_cbrt_down_spec
      -- Need: 0 < g, a < (g+1)³ (i.e., x < (g+1)³), xn0 = Newton(g), x ≥ 1, g ≤ 2^22.
      have h_x_ub_g : x.toNat < (g.toNat + 1) * (g.toNat + 1) * (g.toNat + 1) := by
        -- x ≤ g³ (from hg_cube_ge), and g³ < (g+1)³ since (g+1)³ = g³ + 3g² + 3g + 1 > g³.
        have h_succ_cube := nat_succ_cube g.toNat
        omega
      have h_a_pos : 1 ≤ x.toNat := by omega
      obtain ⟨r, hr_eq, hr_lb, hr_ub⟩ :=
        fixpoint_cbrt_down_spec x g ((x / (g * g) + g * 2) / 3) hg_pos h_x_ub_g h_xn0N' h_a_pos hg_le
      exact ⟨r, hr_eq, hr_lb, hr_ub⟩

/-! ## Contract clauses derived from the master postcondition. -/

/-- Totality / no-panic. The Rust source has no `panic!`; failure modes
    (`/?` divisor of zero on the first Newton step, `*?`/`+?` overflow
    on `x*x`/`a/(x*x) + 2*x`, `<<<?`/`>>>?` shift-overflow on the
    `icbrt2` and `pow2_loop` helpers) are all ruled out by the
    branch-specific invariants summarised in `cbrt_postcondition`. -/
theorem cbrt_total (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := cbrt_postcondition x
  exact ⟨r, hr⟩

/-- Lower bound (independent clause): `cbrt(x)³ ≤ x`. Captures the Rust
    property test `prop_cube_le_x` directly. A buggy implementation that
    returns too large a value (e.g. `x` itself for `x ≥ 2`, or
    `cbrt x + 1` on non-perfect cubes) is caught here. Stated at
    `Nat`-level so that the `checked_pow(3)` guard from the Rust test
    (which only triggers for incorrect oversize results) drops out. -/
theorem cbrt_lower_bound (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ x.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := cbrt_postcondition x
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause): `x < (cbrt(x) + 1)³`. Captures the
    Rust property test `prop_x_lt_next_cube`. Independent from the lower
    bound: an implementation that always returns `0` would pass the
    lower bound but fail this one. Stated at `Nat`-level: the Rust
    test's "modulo overflow" vacuous case (when `(r+1)³` doesn't fit in
    `u64`) becomes the genuine inequality `x.toNat < (r+1)³` in `Nat`,
    which still holds since `x.toNat < 2^64 ≤ (r+1)³` in that regime. -/
theorem cbrt_upper_bound (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
      x.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := cbrt_postcondition x
  exact ⟨r, hr, hub⟩

/-! ## Boundary cases (small-input early-return arm)

The Rust source dispatches `a < 8` via an explicit early-return that
sidesteps the `icbrt2` / Newton iteration: `cbrt 0 = 0`, `cbrt {1..7} = 1`.
These are corollaries of the master postcondition but pin the explicit
code path that the loop helpers never see. From the `cbrt_small_values`
test. -/

/-- Boundary case `cbrt 0 = 0`. Pins the `a = 0` arm of the early-return
    branch (`if a > 0 ... else 0`). Captures `cbrt(0) = 0` from
    `cbrt_small_values`. -/
theorem cbrt_zero : cbrt_u64.cbrt 0 = RustM.ok 0 := by
  unfold cbrt_u64.cbrt
  rfl

/-- Boundary case `cbrt 1 = 1`. Pins the `0 < a < 8` arm of the
    early-return branch. Captures `cbrt(1) = 1` from
    `cbrt_small_values`. -/
theorem cbrt_one : cbrt_u64.cbrt 1 = RustM.ok 1 := by
  unfold cbrt_u64.cbrt
  rfl

end Cbrt_u64Obligations
