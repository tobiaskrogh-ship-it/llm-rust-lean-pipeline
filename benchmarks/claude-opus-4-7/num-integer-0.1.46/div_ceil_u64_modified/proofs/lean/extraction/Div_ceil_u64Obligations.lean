-- Companion obligations file for the `div_ceil_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import div_ceil_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Div_ceil_u64Obligations

/-- Failure condition (precondition violation):
    when `y = 0`, `div_ceil` panics with `Error.divisionByZero`. -/
theorem div_ceil_div_by_zero_failure (x : u64) :
    div_ceil_u64.div_ceil x 0 = RustM.fail .divisionByZero := by
  rfl

/-- Helper: positivity of `y.toNat` when `y : u64` is non-zero. -/
private theorem y_toNat_pos {y : u64} (hy : y ≠ 0) : 0 < y.toNat := by
  have h : y.toNat ≠ 0 := by
    intro h0
    apply hy
    apply UInt64.toNat_inj.mp
    show y.toNat = (0 : UInt64).toNat
    rw [h0]; rfl
  omega

/-- Helper: extract `q = v` from `RustM.ok v = RustM.ok q`. -/
private theorem rustM_ok_inj {v q : u64} (h : (RustM.ok v : RustM u64) = RustM.ok q) :
    q = v := by
  injection h with h1
  injection h1 with h2
  exact h2.symm

/-- Helper: `Nat.div_add_mod` with `(n / k) * k` ordering. -/
private theorem nat_div_add_mod' (n k : Nat) :
    n = (n / k) * k + n % k := by
  have h := Nat.div_add_mod n k
  have hcomm : k * (n / k) = (n / k) * k := Nat.mul_comm _ _
  omega

/-- Postcondition (exact-division case):
    when `y ≠ 0` and `y` divides `x`, `div_ceil` returns `x / y`. -/
theorem div_ceil_postcondition_exact (x y : u64) (hy : y ≠ 0)
    (hexact : x.toNat % y.toNat = 0) :
    div_ceil_u64.div_ceil x y = RustM.ok (UInt64.ofNat (x.toNat / y.toNat)) := by
  have hbound : x.toNat / y.toNat < 2 ^ 64 := by
    have hx : x.toNat < 2 ^ 64 := x.toNat_lt
    have h1 : x.toNat / y.toNat ≤ x.toNat := Nat.div_le_self _ _
    omega
  have hmod_zero : x % y = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod]
    show x.toNat % y.toNat = (0 : UInt64).toNat
    rw [hexact]; rfl
  have hdiv_eq : x / y = UInt64.ofNat (x.toNat / y.toNat) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' hbound]
  unfold div_ceil_u64.div_ceil
  simp only [rust_primitives.ops.arith.Div.div, rust_primitives.ops.arith.Rem.rem,
             rust_primitives.cmp.eq, if_neg hy, pure_bind]
  -- After simp_only, the do-block reduces to a single Bool-condition `if`.
  -- The condition is `(x % y == 0) = true`. Use `hmod_zero` to make it true.
  have h_beq_true : (x % y == (0 : u64)) = true := by
    rw [hmod_zero]; rfl
  rw [if_pos h_beq_true]
  rw [hdiv_eq]
  rfl

/-- Postcondition (non-exact-division case):
    when `y ≠ 0` and `y` does NOT divide `x`, `div_ceil` returns `(x / y) + 1`.
    The `+ 1` cannot overflow `u64` because `x.toNat % y.toNat ≠ 0` forces
    `y.toNat ≥ 2` (since `x % 1 = 0` always), and then
    `2 * (x.toNat / y.toNat) ≤ y.toNat * (x.toNat / y.toNat) ≤ x.toNat < 2^64`,
    so `x.toNat / y.toNat + 1 < 2^64`. -/
theorem div_ceil_postcondition_inexact (x y : u64) (hy : y ≠ 0)
    (hinexact : x.toNat % y.toNat ≠ 0) :
    div_ceil_u64.div_ceil x y =
      RustM.ok (UInt64.ofNat (x.toNat / y.toNat + 1)) := by
  have h_y_pos : 0 < y.toNat := y_toNat_pos hy
  have hyne1 : y.toNat ≠ 1 := by
    intro h
    apply hinexact
    rw [h]; exact Nat.mod_one _
  have hyge2 : y.toNat ≥ 2 := by omega
  have hx_lt : x.toNat < 2 ^ 64 := x.toNat_lt
  have h_div_mul_y : (x.toNat / y.toNat) * y.toNat ≤ x.toNat :=
    Nat.div_mul_le_self _ _
  have h_2_div_le : 2 * (x.toNat / y.toNat) ≤ x.toNat := by
    have h_mul_le : 2 * (x.toNat / y.toNat) ≤ y.toNat * (x.toNat / y.toNat) :=
      Nat.mul_le_mul_right _ hyge2
    have h_comm : y.toNat * (x.toNat / y.toNat) = (x.toNat / y.toNat) * y.toNat :=
      Nat.mul_comm _ _
    omega
  have h_div_succ_lt : x.toNat / y.toNat + 1 < 2 ^ 64 := by omega
  have hmod_ne : x % y ≠ 0 := by
    intro h
    apply hinexact
    have h1 : (x % y).toNat = (0 : UInt64).toNat := by rw [h]
    rw [UInt64.toNat_mod] at h1
    have h0 : (0 : UInt64).toNat = 0 := rfl
    omega
  have h_div_toNat : (x / y).toNat = x.toNat / y.toNat := UInt64.toNat_div _ _
  have h_one_toNat : (1 : UInt64).toNat = 1 := rfl
  have h_no_ovf_nat : (x / y).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    rw [h_div_toNat, h_one_toNat]; omega
  -- The BitVec-overflow check in the un-normalized form (what simp_only leaves).
  have h_no_ovf_bv : (x / y).toBitVec.uaddOverflow (UInt64.toBitVec 1) = false := by
    cases h_eq : (x / y).toBitVec.uaddOverflow (UInt64.toBitVec 1)
    · rfl
    · exfalso
      have h : UInt64.addOverflow (x / y) 1 = true := h_eq
      rw [UInt64.addOverflow_iff] at h
      rw [h_div_toNat, h_one_toNat] at h
      omega
  have h_add_eq : (x / y) + 1 = UInt64.ofNat (x.toNat / y.toNat + 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add_of_lt h_no_ovf_nat]
    rw [h_div_toNat, h_one_toNat]
    rw [UInt64.toNat_ofNat_of_lt' h_div_succ_lt]
  -- The Bool-form `(x % y == 0) ≠ true` follows from `hmod_ne`.
  have h_beq_ne_true : (x % y == (0 : u64)) ≠ true := by
    intro h
    exact hmod_ne (beq_iff_eq.mp h)
  unfold div_ceil_u64.div_ceil
  simp only [rust_primitives.ops.arith.Div.div, rust_primitives.ops.arith.Rem.rem,
             rust_primitives.cmp.eq, if_neg hy, pure_bind]
  -- Goal: `if (x % y == 0) = true then pure (x/y) else (x/y) +? 1 = RustM.ok (...)`.
  rw [if_neg h_beq_ne_true]
  -- Goal: `(x / y) +? 1 = RustM.ok (UInt64.ofNat (...))`. Unfold `+?`.
  show rust_primitives.ops.arith.Add.add (x / y) (1 : u64)
        = RustM.ok (UInt64.ofNat (x.toNat / y.toNat + 1))
  simp only [rust_primitives.ops.arith.Add.add]
  -- Goal involves `if (x / y).toBitVec.uaddOverflow (UInt64.toBitVec 1) = true then ... else ...`.
  rw [if_neg (show ¬ ((x / y).toBitVec.uaddOverflow (UInt64.toBitVec 1) = true) by
              rw [h_no_ovf_bv]; intro h; exact Bool.false_ne_true h)]
  rw [h_add_eq]
  rfl

/-- Postcondition (smallest-q characterization, lower bound):
    for every valid call (`y ≠ 0`), `q.toNat * y.toNat ≥ x.toNat`. -/
theorem div_ceil_lower_bound (x y q : u64) (hy : y ≠ 0)
    (hres : div_ceil_u64.div_ceil x y = RustM.ok q) :
    q.toNat * y.toNat ≥ x.toNat := by
  have h_y_pos : 0 < y.toNat := y_toNat_pos hy
  have hx_lt : x.toNat < 2 ^ 64 := x.toNat_lt
  by_cases hexact : x.toNat % y.toNat = 0
  · rw [div_ceil_postcondition_exact x y hy hexact] at hres
    have hbound : x.toNat / y.toNat < 2 ^ 64 := by
      have h1 : x.toNat / y.toNat ≤ x.toNat := Nat.div_le_self _ _
      omega
    have heq : q = UInt64.ofNat (x.toNat / y.toNat) := rustM_ok_inj hres
    rw [heq, UInt64.toNat_ofNat_of_lt' hbound]
    have hdiv_mod : x.toNat = (x.toNat / y.toNat) * y.toNat + x.toNat % y.toNat :=
      nat_div_add_mod' x.toNat y.toNat
    omega
  · rw [div_ceil_postcondition_inexact x y hy hexact] at hres
    have hyne1 : y.toNat ≠ 1 := by
      intro h; apply hexact; rw [h]; exact Nat.mod_one _
    have hyge2 : y.toNat ≥ 2 := by omega
    have h_div_mul_y : (x.toNat / y.toNat) * y.toNat ≤ x.toNat :=
      Nat.div_mul_le_self _ _
    have h_mul_le : 2 * (x.toNat / y.toNat) ≤ y.toNat * (x.toNat / y.toNat) :=
      Nat.mul_le_mul_right _ hyge2
    have h_comm : y.toNat * (x.toNat / y.toNat) = (x.toNat / y.toNat) * y.toNat :=
      Nat.mul_comm _ _
    have h_2_div_le : 2 * (x.toNat / y.toNat) ≤ x.toNat := by omega
    have h_div_succ_lt : x.toNat / y.toNat + 1 < 2 ^ 64 := by omega
    have heq : q = UInt64.ofNat (x.toNat / y.toNat + 1) := rustM_ok_inj hres
    rw [heq, UInt64.toNat_ofNat_of_lt' h_div_succ_lt]
    have h_expand : (x.toNat / y.toNat + 1) * y.toNat
                      = (x.toNat / y.toNat) * y.toNat + y.toNat := by
      rw [Nat.add_mul, Nat.one_mul]
    have hdiv_mod : x.toNat = (x.toNat / y.toNat) * y.toNat + x.toNat % y.toNat :=
      nat_div_add_mod' x.toNat y.toNat
    have hmod_lt : x.toNat % y.toNat < y.toNat := Nat.mod_lt _ h_y_pos
    omega

/-- Postcondition (smallest-q characterization, minimality):
    for `q > 0`, `(q.toNat - 1) * y.toNat < x.toNat`. -/
theorem div_ceil_minimality (x y q : u64) (hy : y ≠ 0)
    (hpos : q.toNat > 0)
    (hres : div_ceil_u64.div_ceil x y = RustM.ok q) :
    (q.toNat - 1) * y.toNat < x.toNat := by
  have h_y_pos : 0 < y.toNat := y_toNat_pos hy
  have hx_lt : x.toNat < 2 ^ 64 := x.toNat_lt
  by_cases hexact : x.toNat % y.toNat = 0
  · rw [div_ceil_postcondition_exact x y hy hexact] at hres
    have hbound : x.toNat / y.toNat < 2 ^ 64 := by
      have h1 : x.toNat / y.toNat ≤ x.toNat := Nat.div_le_self _ _
      omega
    have heq : q = UInt64.ofNat (x.toNat / y.toNat) := rustM_ok_inj hres
    have hq_toNat : q.toNat = x.toNat / y.toNat := by
      rw [heq, UInt64.toNat_ofNat_of_lt' hbound]
    rw [hq_toNat]
    have hdiv_mod : x.toNat = (x.toNat / y.toNat) * y.toNat + x.toNat % y.toNat :=
      nat_div_add_mod' x.toNat y.toNat
    have hq_pos : x.toNat / y.toNat ≥ 1 := by rw [← hq_toNat]; exact hpos
    have h_x_eq : x.toNat = (x.toNat / y.toNat) * y.toNat := by omega
    have h_factor :
        (x.toNat / y.toNat - 1) * y.toNat + y.toNat
          = (x.toNat / y.toNat) * y.toNat := by
      have h_split : x.toNat / y.toNat - 1 + 1 = x.toNat / y.toNat := by omega
      calc (x.toNat / y.toNat - 1) * y.toNat + y.toNat
          = (x.toNat / y.toNat - 1) * y.toNat + 1 * y.toNat := by rw [Nat.one_mul]
        _ = (x.toNat / y.toNat - 1 + 1) * y.toNat := by rw [Nat.add_mul]
        _ = (x.toNat / y.toNat) * y.toNat := by rw [h_split]
    omega
  · rw [div_ceil_postcondition_inexact x y hy hexact] at hres
    have hyne1 : y.toNat ≠ 1 := by
      intro h; apply hexact; rw [h]; exact Nat.mod_one _
    have hyge2 : y.toNat ≥ 2 := by omega
    have h_div_mul_y : (x.toNat / y.toNat) * y.toNat ≤ x.toNat :=
      Nat.div_mul_le_self _ _
    have h_mul_le : 2 * (x.toNat / y.toNat) ≤ y.toNat * (x.toNat / y.toNat) :=
      Nat.mul_le_mul_right _ hyge2
    have h_comm : y.toNat * (x.toNat / y.toNat) = (x.toNat / y.toNat) * y.toNat :=
      Nat.mul_comm _ _
    have h_2_div_le : 2 * (x.toNat / y.toNat) ≤ x.toNat := by omega
    have h_div_succ_lt : x.toNat / y.toNat + 1 < 2 ^ 64 := by omega
    have heq : q = UInt64.ofNat (x.toNat / y.toNat + 1) := rustM_ok_inj hres
    have hq_toNat : q.toNat = x.toNat / y.toNat + 1 := by
      rw [heq, UInt64.toNat_ofNat_of_lt' h_div_succ_lt]
    rw [hq_toNat]
    have h_simp : x.toNat / y.toNat + 1 - 1 = x.toNat / y.toNat := by omega
    rw [h_simp]
    have hdiv_mod : x.toNat = (x.toNat / y.toNat) * y.toNat + x.toNat % y.toNat :=
      nat_div_add_mod' x.toNat y.toNat
    have hmod_pos : 0 < x.toNat % y.toNat := Nat.pos_of_ne_zero hexact
    omega

end Div_ceil_u64Obligations
