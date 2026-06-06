-- Companion obligations file for the `clever_130_digits` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_130_digits

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_130_digitsObligations

/-! ## Nat-level oracles for the contract -/

/-- Walk through the decimal digits of `n` (high to low via `/ 10`), folding
    the product of odd digits into `acc`. The Bool flag `any_odd` tracks
    whether any odd digit has been observed; if none has when the recursion
    bottoms out at `n = 0`, the final result is `0` rather than the empty
    product `acc`. Mirrors the Rust `walk_at` helper exactly. -/
private def walk_at_nat (n acc : Nat) (any_odd : Bool) : Nat :=
  if h : 0 < n then
    if (n % 10) % 2 = 1 then
      walk_at_nat (n / 10) (acc * (n % 10)) true
    else
      walk_at_nat (n / 10) acc any_odd
  else
    if any_odd then acc else 0
termination_by n
decreasing_by all_goals exact Nat.div_lt_self h (by decide)

/-- Product of the odd decimal digits of `n`, or `0` if `n = 0` or `n` has
    no odd digit at all. Mirrors the Rust `digits` wrapper. -/
private def digits_nat (n : Nat) : Nat :=
  if n = 0 then 0 else walk_at_nat n 1 false

/-- Predicate: every decimal digit of `n` is even (vacuously `true` when
    `n = 0`). Used to phrase the all-even special case. -/
private def all_digits_even_nat (n : Nat) : Bool :=
  if h : 0 < n then
    (n % 10 % 2 == 0) && all_digits_even_nat (n / 10)
  else
    true
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-! ## Scaffolding helpers. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_ten_toNat : (10 : u64).toNat = 10 := rfl

private theorem u64_ofNat_toNat_of_lt (x : Nat) (h : x < 2 ^ 64) :
    (UInt64.ofNat x).toNat = x :=
  UInt64.toNat_ofNat_of_lt' h

private theorem mod_pure (a b : u64) (h : b ≠ 0) :
    (a %? b : RustM u64) = pure (a % b) := by
  show (rust_primitives.ops.arith.Rem.rem a b : RustM u64) = pure (a % b)
  show (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a % b)) = _
  rw [if_neg h]

private theorem div_pure (a b : u64) (h : b ≠ 0) :
    (a /? b : RustM u64) = pure (a / b) := by
  show (rust_primitives.ops.arith.Div.div a b : RustM u64) = pure (a / b)
  show (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a / b)) = _
  rw [if_neg h]

private theorem mul_pure (a b : u64) (h : a.toNat * b.toNat < 2 ^ 64) :
    (a *? b : RustM u64) = pure (a * b) := by
  show (rust_primitives.ops.arith.Mul.mul a b : RustM u64) = pure (a * b)
  show (if BitVec.umulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a * b)) = _
  have h_no : ¬ UInt64.mulOverflow a b := by rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow a.toBitVec b.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

private theorem u64_eq_test (a b : u64) :
    (a ==? b : RustM Bool) = pure (decide (a = b)) := rfl

private theorem u64_toNat_pos_of_ne_zero (n : u64) (h : n ≠ 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with h_zero | h_pos
  · exfalso; apply h
    have : n.toNat = (0 : u64).toNat := by rw [h_zero]; rfl
    exact UInt64.toNat_inj.mp this
  · exact h_pos

/-! ## Equations for `walk_at_nat`. -/

private theorem walk_at_nat_zero (acc : Nat) (b : Bool) :
    walk_at_nat 0 acc b = if b then acc else 0 := by
  conv => lhs; unfold walk_at_nat
  rw [dif_neg (by decide : ¬ 0 < 0)]

private theorem walk_at_nat_zero_true (acc : Nat) :
    walk_at_nat 0 acc true = acc := by
  rw [walk_at_nat_zero]; simp

private theorem walk_at_nat_zero_false (acc : Nat) :
    walk_at_nat 0 acc false = 0 := by
  rw [walk_at_nat_zero]; simp

private theorem walk_at_nat_succ_odd (n acc : Nat) (b : Bool)
    (h : 0 < n) (h_odd : n % 10 % 2 = 1) :
    walk_at_nat n acc b = walk_at_nat (n / 10) (acc * (n % 10)) true := by
  conv => lhs; unfold walk_at_nat
  rw [dif_pos h, if_pos h_odd]

private theorem walk_at_nat_succ_even (n acc : Nat) (b : Bool)
    (h : 0 < n) (h_even : ¬ n % 10 % 2 = 1) :
    walk_at_nat n acc b = walk_at_nat (n / 10) acc b := by
  conv => lhs; unfold walk_at_nat
  rw [dif_pos h, if_neg h_even]

/-! ## Bound on `walk_at_nat`. -/

private theorem walk_at_nat_le_mul_pow :
    ∀ (k : Nat) (n acc : Nat) (b : Bool),
      n < 10 ^ k → walk_at_nat n acc b ≤ acc * 9 ^ k := by
  intro k
  induction k with
  | zero =>
    intro n acc b h
    have h_n : n = 0 := by simpa using h
    cases b with
    | false =>
      rw [h_n, walk_at_nat_zero_false]; exact Nat.zero_le _
    | true =>
      rw [h_n, walk_at_nat_zero_true, Nat.pow_zero, Nat.mul_one]
      exact Nat.le_refl _
  | succ k ih =>
    intro n acc b h
    have h_pow10 : (10 : Nat) ^ (k + 1) = 10 * 10 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h_pow9 : (9 : Nat) ^ (k + 1) = 9 * 9 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hn : 0 < n
    · have h_div : n / 10 < 10 ^ k := by
        rw [h_pow10] at h
        exact Nat.div_lt_of_lt_mul h
      have h_mod_le : n % 10 ≤ 9 :=
        Nat.lt_succ_iff.mp (Nat.mod_lt n (by decide))
      by_cases h_odd : n % 10 % 2 = 1
      · rw [walk_at_nat_succ_odd n acc b hn h_odd]
        have ih_app := ih (n / 10) (acc * (n % 10)) true h_div
        calc walk_at_nat (n / 10) (acc * (n % 10)) true
            ≤ acc * (n % 10) * 9 ^ k := ih_app
          _ ≤ acc * 9 * 9 ^ k := by
              apply Nat.mul_le_mul_right
              exact Nat.mul_le_mul_left acc h_mod_le
          _ = acc * (9 * 9 ^ k) := by rw [Nat.mul_assoc]
          _ = acc * 9 ^ (k + 1) := by rw [h_pow9]
      · rw [walk_at_nat_succ_even n acc b hn h_odd]
        have ih_app := ih (n / 10) acc b h_div
        have h_pow_le : (9 : Nat) ^ k ≤ 9 ^ (k + 1) := by
          rw [h_pow9]
          calc (9 : Nat) ^ k = 1 * 9 ^ k := by rw [Nat.one_mul]
            _ ≤ 9 * 9 ^ k := Nat.mul_le_mul_right _ (by decide)
        calc walk_at_nat (n / 10) acc b
            ≤ acc * 9 ^ k := ih_app
          _ ≤ acc * 9 ^ (k + 1) := Nat.mul_le_mul_left _ h_pow_le
    · have h_n_zero : n = 0 := by omega
      have h_pow_pos : 0 < (9 : Nat) ^ (k + 1) :=
        Nat.pow_pos (by decide : (0 : Nat) < 9)
      cases b with
      | false =>
        rw [h_n_zero, walk_at_nat_zero_false]; exact Nat.zero_le _
      | true =>
        rw [h_n_zero, walk_at_nat_zero_true]
        show acc ≤ acc * 9 ^ (k + 1)
        have : acc * 1 ≤ acc * 9 ^ (k + 1) :=
          Nat.mul_le_mul_left acc h_pow_pos
        rw [Nat.mul_one] at this
        exact this

/-! ## All-even-digits implies zero result for `walk_at_nat`. -/

private theorem all_digits_even_nat_zero :
    all_digits_even_nat 0 = true := by
  conv => lhs; unfold all_digits_even_nat
  rw [dif_neg (by decide : ¬ 0 < 0)]

private theorem all_digits_even_nat_succ (n : Nat) (h : 0 < n) :
    all_digits_even_nat n =
      ((n % 10 % 2 == 0) && all_digits_even_nat (n / 10)) := by
  conv => lhs; unfold all_digits_even_nat
  rw [dif_pos h]

private theorem walk_at_nat_all_even :
    ∀ (m : Nat) (n acc : Nat),
      n ≤ m → all_digits_even_nat n = true →
      walk_at_nat n acc false = 0 := by
  intro m
  induction m with
  | zero =>
    intro n acc hm h
    have hn : n = 0 := by omega
    rw [hn, walk_at_nat_zero]
    rfl
  | succ m ih =>
    intro n acc hm h
    by_cases hn : 0 < n
    · rw [all_digits_even_nat_succ n hn] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h_mod_even, h_rest⟩ := h
      have h_not_odd : ¬ n % 10 % 2 = 1 := by
        rw [h_mod_even]; decide
      rw [walk_at_nat_succ_even n acc false hn h_not_odd]
      have h_div_le : n / 10 ≤ m := by
        have h_div_lt : n / 10 < n := Nat.div_lt_self hn (by decide)
        omega
      exact ih (n / 10) acc h_div_le h_rest
    · have h_n_zero : n = 0 := by omega
      rw [h_n_zero, walk_at_nat_zero]
      rfl

/-! ## Pointwise correctness of `walk_at`.

Strong induction on `n.toNat` with a parameter `k` carrying the digit-bound
invariant. The bound `acc.toNat * 9 ^ k < 2 ^ 64` is preserved across each
step (a multiplication by at most `9` is offset by a decrement of `k`). -/

/-- Base case at `n = 0`. Case-split on `any_odd` makes both sides
    definitionally compare cleanly without `if true = true` shenanigans. -/
private theorem walk_at_zero_correct (acc : u64) (b : Bool) :
    clever_130_digits.walk_at 0 acc b
      = RustM.ok (UInt64.ofNat (walk_at_nat 0 acc.toNat b)) := by
  unfold clever_130_digits.walk_at
  rw [u64_eq_test]
  simp only [pure_bind]
  cases b with
  | false =>
    rw [walk_at_nat_zero_false]
    show pure (0 : u64) = RustM.ok (UInt64.ofNat 0)
    rfl
  | true =>
    rw [walk_at_nat_zero_true]
    show pure acc = RustM.ok (UInt64.ofNat acc.toNat)
    apply congrArg
    apply UInt64.toNat_inj.mp
    rw [u64_ofNat_toNat_of_lt acc.toNat acc.toNat_lt]

private theorem walk_at_correct :
    ∀ (m : Nat) (n acc : u64) (b : Bool) (k : Nat),
      n.toNat ≤ m →
      n.toNat < 10 ^ k →
      acc.toNat * 9 ^ k < 2 ^ 64 →
      clever_130_digits.walk_at n acc b
        = RustM.ok (UInt64.ofNat (walk_at_nat n.toNat acc.toNat b)) := by
  intro m
  induction m with
  | zero =>
    intro n acc b k hm h_lt h_bound
    have h_n_zero : n.toNat = 0 := by omega
    have h_n_eq : n = 0 :=
      UInt64.toNat_inj.mp (by rw [h_n_zero]; rfl)
    subst h_n_eq
    exact walk_at_zero_correct acc b
  | succ m ih =>
    intro n acc b k hm h_lt h_bound
    by_cases h_n_zero : n = 0
    · subst h_n_zero
      exact walk_at_zero_correct acc b
    · have hn_pos : 0 < n.toNat := u64_toNat_pos_of_ne_zero n h_n_zero
      -- Choose k > 0 in this branch.
      have h_k_pos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
        · exfalso
          rw [hk0, Nat.pow_zero] at h_lt
          omega
        · exact hk_pos
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h_pow10 : (10 : Nat) ^ (k' + 1) = 10 * 10 ^ k' := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have h_pow9 : (9 : Nat) ^ (k' + 1) = 9 * 9 ^ k' := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have h_n_div_lt : n.toNat / 10 < 10 ^ k' := by
        rw [h_pow10] at h_lt
        exact Nat.div_lt_of_lt_mul h_lt
      unfold clever_130_digits.walk_at
      rw [u64_eq_test]
      have h_dec : decide (n = (0 : u64)) = false := decide_eq_false h_n_zero
      simp only [pure_bind, h_dec, Bool.false_eq_true, ↓reduceIte]
      rw [mod_pure n 10 (by decide : (10 : u64) ≠ 0)]
      simp only [pure_bind]
      rw [mod_pure (n % 10) 2 (by decide : (2 : u64) ≠ 0)]
      simp only [pure_bind]
      rw [u64_eq_test]
      simp only [pure_bind]
      have h_mod10_toNat : (n % 10).toNat = n.toNat % 10 := by
        rw [UInt64.toNat_mod, u64_ten_toNat]
      have h_mod10_2_toNat : ((n % 10) % 2).toNat = n.toNat % 10 % 2 := by
        rw [UInt64.toNat_mod, h_mod10_toNat, u64_two_toNat]
      have h_div10_toNat : (n / 10).toNat = n.toNat / 10 := by
        rw [UInt64.toNat_div, u64_ten_toNat]
      have h_div_le_m : (n / 10).toNat ≤ m := by
        rw [h_div10_toNat]
        have : n.toNat / 10 < n.toNat := Nat.div_lt_self hn_pos (by decide)
        omega
      have h_div_acc_bound : (n / 10).toNat < 10 ^ k' := by
        rw [h_div10_toNat]; exact h_n_div_lt
      have h_mod_le_9 : n.toNat % 10 ≤ 9 :=
        Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      -- 9 * 9^k' = 9^(k'+1) bound on acc * mod10 bound chain
      have h_step9 : acc.toNat * (n.toNat % 10) * 9 ^ k' ≤ acc.toNat * 9 ^ (k' + 1) := by
        calc acc.toNat * (n.toNat % 10) * 9 ^ k'
            ≤ acc.toNat * 9 * 9 ^ k' := by
              apply Nat.mul_le_mul_right
              exact Nat.mul_le_mul_left acc.toNat h_mod_le_9
          _ = acc.toNat * (9 * 9 ^ k') := by rw [Nat.mul_assoc]
          _ = acc.toNat * 9 ^ (k' + 1) := by rw [h_pow9]
      by_cases h_odd : (n % 10) % 2 = (1 : u64)
      · have h_dec_odd : decide ((n % 10) % 2 = (1 : u64)) = true :=
          decide_eq_true h_odd
        rw [h_dec_odd]
        simp only [↓reduceIte]
        have h_mod_nat_odd : n.toNat % 10 % 2 = 1 := by
          have h_t : ((n % 10) % 2).toNat = (1 : u64).toNat := by rw [h_odd]
          rw [h_mod10_2_toNat, u64_one_toNat] at h_t
          exact h_t
        -- Compute (n /? 10) and (acc *? d).
        rw [div_pure n 10 (by decide : (10 : u64) ≠ 0)]
        simp only [pure_bind]
        have h_mul_bound : acc.toNat * (n % 10).toNat < 2 ^ 64 := by
          rw [h_mod10_toNat]
          have h_pow_pos : 0 < (9 : Nat) ^ k' :=
            Nat.pow_pos (by decide : (0 : Nat) < 9)
          have h_left : acc.toNat * (n.toNat % 10)
              ≤ acc.toNat * (n.toNat % 10) * 9 ^ k' :=
            Nat.le_mul_of_pos_right (acc.toNat * (n.toNat % 10)) h_pow_pos
          omega
        rw [mul_pure acc (n % 10) h_mul_bound]
        simp only [pure_bind]
        have h_acc_mul_toNat : (acc * (n % 10)).toNat = acc.toNat * (n.toNat % 10) := by
          rw [UInt64.toNat_mul_of_lt h_mul_bound, h_mod10_toNat]
        have h_new_bound : (acc * (n % 10)).toNat * 9 ^ k' < 2 ^ 64 := by
          rw [h_acc_mul_toNat]
          have h_left : acc.toNat * (n.toNat % 10) * 9 ^ k'
              ≤ acc.toNat * 9 ^ (k' + 1) := h_step9
          omega
        rw [ih (n / 10) (acc * (n % 10)) true k' h_div_le_m h_div_acc_bound h_new_bound]
        apply congrArg
        congr 1
        rw [walk_at_nat_succ_odd n.toNat acc.toNat b hn_pos h_mod_nat_odd]
        rw [h_div10_toNat, h_acc_mul_toNat]
      · have h_dec_odd : decide ((n % 10) % 2 = (1 : u64)) = false :=
          decide_eq_false h_odd
        rw [h_dec_odd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [div_pure n 10 (by decide : (10 : u64) ≠ 0)]
        simp only [pure_bind]
        have h_mod_nat_not_odd : ¬ n.toNat % 10 % 2 = 1 := by
          intro h_eq
          apply h_odd
          apply UInt64.toNat_inj.mp
          rw [h_mod10_2_toNat, u64_one_toNat]
          exact h_eq
        have h_new_bound : acc.toNat * 9 ^ k' < 2 ^ 64 := by
          have h9pow_le : (9 : Nat) ^ k' ≤ 9 ^ (k' + 1) := by
            rw [h_pow9]
            calc (9 : Nat) ^ k' = 1 * 9 ^ k' := by rw [Nat.one_mul]
              _ ≤ 9 * 9 ^ k' := Nat.mul_le_mul_right _ (by decide)
          have : acc.toNat * 9 ^ k' ≤ acc.toNat * 9 ^ (k' + 1) :=
            Nat.mul_le_mul_left _ h9pow_le
          omega
        rw [ih (n / 10) acc b k' h_div_le_m h_div_acc_bound h_new_bound]
        apply congrArg
        congr 1
        rw [walk_at_nat_succ_even n.toNat acc.toNat b hn_pos h_mod_nat_not_odd]
        rw [h_div10_toNat]

/-! ## Bound `n.toNat < 10 ^ 20` for any `u64 n`. -/

private theorem u64_toNat_lt_pow20 (n : u64) : n.toNat < 10 ^ 20 := by
  have h1 : n.toNat < 2 ^ 64 := n.toNat_lt
  have h2 : (2 : Nat) ^ 64 ≤ 10 ^ 20 := by decide
  omega

private theorem nine_pow_20_lt : (1 : Nat) * 9 ^ 20 < 2 ^ 64 := by decide

/-! ## Main contract clauses

The Rust source (`mod tests`) carries two proptests and one `known`
unit-tests block. Each contract-style assertion gets one theorem below.

* `prop_matches_reference` — main functional postcondition on every
  `u64`.  Feasibility: the product of odd decimal digits of any
  `u64` is at most `9^20 = 12_157_665_459_056_928_801 < 2^64`, so the
  universal version is true in the Lean model with no precondition.
* `prop_all_even_digits_returns_zero` — the empty-odd-set convention.
* `known` — six concrete pins closed by `native_decide`. -/

/-- Main postcondition: for every `u64 n`, `digits n` succeeds and equals
    the product of the odd decimal digits of `n` (with `0` for `n = 0` or
    the all-even case).  Captures `prop_matches_reference`. -/
theorem digits_matches_reference (n : u64) :
    clever_130_digits.digits n
      = RustM.ok (UInt64.ofNat (digits_nat n.toNat)) := by
  unfold clever_130_digits.digits
  rw [u64_eq_test]
  by_cases h_n_zero : n = 0
  · subst h_n_zero
    simp only [pure_bind]
    show RustM.ok (0 : u64) = _
    apply congrArg
    apply UInt64.toNat_inj.mp
    rw [u64_zero_toNat]
    unfold digits_nat
    simp
  · have h_dec : decide (n = (0 : u64)) = false := decide_eq_false h_n_zero
    simp only [pure_bind, h_dec, Bool.false_eq_true, ↓reduceIte]
    have h_n_toNat : 0 < n.toNat := u64_toNat_pos_of_ne_zero n h_n_zero
    have h_lt20 : n.toNat < 10 ^ 20 := u64_toNat_lt_pow20 n
    have h_bound : (1 : u64).toNat * 9 ^ 20 < 2 ^ 64 := by
      rw [u64_one_toNat]; exact nine_pow_20_lt
    have h_eq := walk_at_correct n.toNat n (1 : u64) false 20
        (Nat.le_refl _) h_lt20 h_bound
    rw [h_eq]
    apply congrArg
    have h_digits_eq : digits_nat n.toNat = walk_at_nat n.toNat (1 : u64).toNat false := by
      unfold digits_nat
      have h_ne : n.toNat ≠ 0 := Nat.pos_iff_ne_zero.mp h_n_toNat
      rw [if_neg h_ne, u64_one_toNat]
    rw [h_digits_eq]

/-- Empty-odd-set convention: when every decimal digit of `n` is even
    (including `n = 0`), `digits n` is exactly `0`, not the empty product
    `1`.  Captures `prop_all_even_digits_returns_zero`. -/
theorem digits_all_even_returns_zero
    (n : u64) (h : all_digits_even_nat n.toNat = true) :
    clever_130_digits.digits n = RustM.ok (0 : u64) := by
  rw [digits_matches_reference n]
  apply congrArg
  apply UInt64.toNat_inj.mp
  rw [u64_zero_toNat]
  unfold digits_nat
  by_cases h_n : n.toNat = 0
  · rw [if_pos h_n]; rfl
  · rw [if_neg h_n]
    have h_walk : walk_at_nat n.toNat 1 false = 0 :=
      walk_at_nat_all_even n.toNat n.toNat 1 (Nat.le_refl _) h
    rw [h_walk]
    rfl

/-! ## Unit pins from `known` -/

/-- `digits 0 = 0`. -/
theorem digits_at_0 :
    clever_130_digits.digits 0 = RustM.ok (0 : u64) := by
  native_decide

/-- `digits 1 = 1`. -/
theorem digits_at_1 :
    clever_130_digits.digits 1 = RustM.ok (1 : u64) := by
  native_decide

/-- `digits 4 = 0` — all (one) digit is even. -/
theorem digits_at_4 :
    clever_130_digits.digits 4 = RustM.ok (0 : u64) := by
  native_decide

/-- `digits 235 = 15` — odd digits `3, 5` give product `15`. -/
theorem digits_at_235 :
    clever_130_digits.digits 235 = RustM.ok (15 : u64) := by
  native_decide

/-- `digits 2468 = 0` — every digit is even. -/
theorem digits_at_2468 :
    clever_130_digits.digits 2468 = RustM.ok (0 : u64) := by
  native_decide

/-- `digits 2222 = 0` — every digit is even. -/
theorem digits_at_2222 :
    clever_130_digits.digits 2222 = RustM.ok (0 : u64) := by
  native_decide

end Clever_130_digitsObligations
