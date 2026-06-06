-- Companion obligations file for the `clever_153_even_odd_count` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_153_even_odd_count

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_153_even_odd_countObligations

/-! ## Nat-level oracle for the contract -/

/-- Walk through the decimal digits of `n` (low to high via `/ 10`),
    incrementing the even-counter `e` for each even digit and the
    odd-counter `o` for each odd digit. Mirrors the Rust `count_at`
    helper exactly. -/
private def count_at_nat (n e o : Nat) : Nat × Nat :=
  if h : 0 < n then
    if (n % 10) % 2 = 0 then count_at_nat (n / 10) (e + 1) o
    else count_at_nat (n / 10) e (o + 1)
  else (e, o)
termination_by n
decreasing_by all_goals exact Nat.div_lt_self h (by decide)

/-- Specification of `even_odd_count(n)` — for `n = 0` we count one digit
    `0` (which is even), giving `(1, 0)`. Otherwise the result is the
    digit-by-digit count produced by `count_at_nat` starting from
    `(e, o) = (0, 0)`. -/
private def even_odd_count_nat (n : Nat) : Nat × Nat :=
  if n = 0 then (1, 0) else count_at_nat n 0 0

/-! ## Scaffolding helpers (lifted verbatim from `clever_130_digits`). -/

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

private theorem add_pure (a b : u64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b : RustM u64) = pure (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM u64) = pure (a + b)
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a + b)) = _
  have h_no : ¬ UInt64.addOverflow a b := by rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow a.toBitVec b.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

private theorem u64_eq_test (a b : u64) :
    (a ==? b : RustM Bool) = pure (decide (a = b)) := rfl

private theorem u64_toNat_pos_of_ne_zero (n : u64) (h : n ≠ 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with h_zero | h_pos
  · exfalso; apply h
    have : n.toNat = (0 : u64).toNat := by rw [h_zero]; rfl
    exact UInt64.toNat_inj.mp this
  · exact h_pos

/-! ## Equations for `count_at_nat`. -/

private theorem count_at_nat_zero (e o : Nat) :
    count_at_nat 0 e o = (e, o) := by
  conv => lhs; unfold count_at_nat
  rw [dif_neg (by decide : ¬ 0 < 0)]

private theorem count_at_nat_succ_even (n e o : Nat)
    (h : 0 < n) (h_even : (n % 10) % 2 = 0) :
    count_at_nat n e o = count_at_nat (n / 10) (e + 1) o := by
  conv => lhs; unfold count_at_nat
  rw [dif_pos h, if_pos h_even]

private theorem count_at_nat_succ_odd (n e o : Nat)
    (h : 0 < n) (h_odd : (n % 10) % 2 ≠ 0) :
    count_at_nat n e o = count_at_nat (n / 10) e (o + 1) := by
  conv => lhs; unfold count_at_nat
  rw [dif_pos h, if_neg h_odd]

/-! ## Bound on `count_at_nat`.

For `n < 10 ^ k`, the recursion processes at most `k` digits, so each
component of the result is bounded by `e + k` or `o + k` respectively.

In fact a tighter invariant holds: the *sum* `(count_at_nat n e o).1 +
(count_at_nat n e o).2 = e + o + d`, where `d` is the number of decimal
digits of `n` (zero when `n = 0`).  We only need the upper bound. -/

private theorem count_at_nat_le :
    ∀ (k : Nat) (n e o : Nat),
      n < 10 ^ k →
      (count_at_nat n e o).1 ≤ e + k ∧
      (count_at_nat n e o).2 ≤ o + k := by
  intro k
  induction k with
  | zero =>
    intro n e o h
    have h_n : n = 0 := by simpa using h
    rw [h_n, count_at_nat_zero]
    exact ⟨by simp, by simp⟩
  | succ k ih =>
    intro n e o h
    by_cases hn : 0 < n
    · have h_pow : (10 : Nat) ^ (k + 1) = 10 * 10 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have h_div_lt : n / 10 < 10 ^ k := by
        rw [h_pow] at h
        exact Nat.div_lt_of_lt_mul h
      by_cases h_even : (n % 10) % 2 = 0
      · rw [count_at_nat_succ_even n e o hn h_even]
        obtain ⟨h1, h2⟩ := ih (n / 10) (e + 1) o h_div_lt
        refine ⟨?_, ?_⟩
        · -- (e + 1) + k = e + (k + 1)
          have : e + 1 + k = e + (k + 1) := by omega
          rw [this] at h1; exact h1
        · have : o + k ≤ o + (k + 1) := by omega
          exact Nat.le_trans h2 this
      · rw [count_at_nat_succ_odd n e o hn h_even]
        obtain ⟨h1, h2⟩ := ih (n / 10) e (o + 1) h_div_lt
        refine ⟨?_, ?_⟩
        · have : e + k ≤ e + (k + 1) := by omega
          exact Nat.le_trans h1 this
        · have : o + 1 + k = o + (k + 1) := by omega
          rw [this] at h2; exact h2
    · have h_zero : n = 0 := by omega
      rw [h_zero, count_at_nat_zero]
      refine ⟨?_, ?_⟩ <;> omega

private theorem count_at_nat_fst_lt (n e o : Nat) (k : Nat)
    (h_lt : n < 10 ^ k) (h_bound : e + o + k < 2 ^ 64) :
    (count_at_nat n e o).1 < 2 ^ 64 := by
  obtain ⟨h1, _⟩ := count_at_nat_le k n e o h_lt
  omega

private theorem count_at_nat_snd_lt (n e o : Nat) (k : Nat)
    (h_lt : n < 10 ^ k) (h_bound : e + o + k < 2 ^ 64) :
    (count_at_nat n e o).2 < 2 ^ 64 := by
  obtain ⟨_, h2⟩ := count_at_nat_le k n e o h_lt
  omega

/-! ## Bound `n.toNat < 10 ^ 20` for any `u64 n`. -/

private theorem u64_toNat_lt_pow20 (n : u64) : n.toNat < 10 ^ 20 := by
  have h1 : n.toNat < 2 ^ 64 := n.toNat_lt
  have h2 : (2 : Nat) ^ 64 ≤ 10 ^ 20 := by decide
  omega

/-! ## Pointwise correctness of `count_at`.

Strong induction on the measure `n.toNat ≤ m` carrying:
- a digit-count parameter `k` with `n.toNat < 10 ^ k`,
- the overflow invariant `e.toNat + o.toNat + k < 2 ^ 64`.

Both invariants are preserved across a single recursive step:
- `n / 10 < 10 ^ (k - 1)` (when `k ≥ 1`, forced by `n > 0`),
- either `e` or `o` grows by `1` while `k` drops by `1`, leaving
  `e + o + k` unchanged.

The bound also guarantees `e + 1 < 2 ^ 64` and `o + 1 < 2 ^ 64`, so the
intermediate `+? 1` always succeeds.
-/

private theorem count_at_correct :
    ∀ (m : Nat) (n e o : u64) (k : Nat),
      n.toNat ≤ m →
      n.toNat < 10 ^ k →
      e.toNat + o.toNat + k < 2 ^ 64 →
      clever_153_even_odd_count.count_at n e o
        = RustM.ok (rust_primitives.hax.Tuple2.mk
            (UInt64.ofNat (count_at_nat n.toNat e.toNat o.toNat).1)
            (UInt64.ofNat (count_at_nat n.toNat e.toNat o.toNat).2)) := by
  intro m
  induction m with
  | zero =>
    intro n e o k hm h_lt h_bound
    have h_n_zero : n.toNat = 0 := by omega
    have h_n_eq : n = 0 :=
      UInt64.toNat_inj.mp (by rw [h_n_zero]; rfl)
    subst h_n_eq
    unfold clever_153_even_odd_count.count_at
    have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
      show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
      rfl
    simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
    rw [show ((0 : u64).toNat = 0) from rfl, count_at_nat_zero]
    show RustM.ok (rust_primitives.hax.Tuple2.mk e o)
        = RustM.ok (rust_primitives.hax.Tuple2.mk
            (UInt64.ofNat e.toNat) (UInt64.ofNat o.toNat))
    have h_e : UInt64.ofNat e.toNat = e :=
      UInt64.toNat_inj.mp
        (by rw [u64_ofNat_toNat_of_lt e.toNat e.toNat_lt])
    have h_o : UInt64.ofNat o.toNat = o :=
      UInt64.toNat_inj.mp
        (by rw [u64_ofNat_toNat_of_lt o.toNat o.toNat_lt])
    rw [h_e, h_o]
  | succ m ih =>
    intro n e o k hm h_lt h_bound
    by_cases h_n_zero : n = 0
    · subst h_n_zero
      unfold clever_153_even_odd_count.count_at
      have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
        show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
        rfl
      simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
      rw [show ((0 : u64).toNat = 0) from rfl, count_at_nat_zero]
      show RustM.ok (rust_primitives.hax.Tuple2.mk e o)
          = RustM.ok (rust_primitives.hax.Tuple2.mk
              (UInt64.ofNat e.toNat) (UInt64.ofNat o.toNat))
      have h_e : UInt64.ofNat e.toNat = e :=
        UInt64.toNat_inj.mp
          (by rw [u64_ofNat_toNat_of_lt e.toNat e.toNat_lt])
      have h_o : UInt64.ofNat o.toNat = o :=
        UInt64.toNat_inj.mp
          (by rw [u64_ofNat_toNat_of_lt o.toNat o.toNat_lt])
      rw [h_e, h_o]
    · have hn_pos : 0 < n.toNat := u64_toNat_pos_of_ne_zero n h_n_zero
      -- We must have k > 0, since n > 0 forces n ≥ 1 ≥ 10^0.
      have h_k_pos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
        · exfalso
          rw [hk0, Nat.pow_zero] at h_lt
          omega
        · exact hk_pos
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h_pow : (10 : Nat) ^ (k' + 1) = 10 * 10 ^ k' := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have h_n_div_lt : n.toNat / 10 < 10 ^ k' := by
        rw [h_pow] at h_lt
        exact Nat.div_lt_of_lt_mul h_lt
      -- Step lemmas on the Rust side.
      unfold clever_153_even_odd_count.count_at
      rw [u64_eq_test]
      have h_dec_ne : decide (n = (0 : u64)) = false := decide_eq_false h_n_zero
      simp only [pure_bind, h_dec_ne, Bool.false_eq_true, ↓reduceIte]
      rw [mod_pure n 10 (by decide : (10 : u64) ≠ 0)]
      simp only [pure_bind]
      rw [mod_pure (n % 10) 2 (by decide : (2 : u64) ≠ 0)]
      simp only [pure_bind]
      rw [u64_eq_test]
      simp only [pure_bind]
      -- Conversion lemmas.
      have h_mod10_toNat : (n % 10).toNat = n.toNat % 10 := by
        rw [UInt64.toNat_mod, u64_ten_toNat]
      have h_mod10_2_toNat : ((n % 10) % 2).toNat = n.toNat % 10 % 2 := by
        rw [UInt64.toNat_mod, h_mod10_toNat, u64_two_toNat]
      have h_div10_toNat : (n / 10).toNat = n.toNat / 10 := by
        rw [UInt64.toNat_div, u64_ten_toNat]
      have h_div_le_m : (n / 10).toNat ≤ m := by
        rw [h_div10_toNat]
        have h_lt_n : n.toNat / 10 < n.toNat := Nat.div_lt_self hn_pos (by decide)
        omega
      -- The +? 1 step uses these:
      have h_e1_bound : e.toNat + (1 : u64).toNat < 2 ^ 64 := by
        rw [u64_one_toNat]; omega
      have h_o1_bound : o.toNat + (1 : u64).toNat < 2 ^ 64 := by
        rw [u64_one_toNat]; omega
      have h_e1_eq : (e +? (1 : u64) : RustM u64) = pure (e + 1) :=
        add_pure e 1 h_e1_bound
      have h_o1_eq : (o +? (1 : u64) : RustM u64) = pure (o + 1) :=
        add_pure o 1 h_o1_bound
      have h_e1_toNat : (e + 1).toNat = e.toNat + 1 := by
        rw [UInt64.toNat_add_of_lt h_e1_bound, u64_one_toNat]
      have h_o1_toNat : (o + 1).toNat = o.toNat + 1 := by
        rw [UInt64.toNat_add_of_lt h_o1_bound, u64_one_toNat]
      by_cases h_even : (n % 10) % 2 = (0 : u64)
      · -- Even branch.
        have h_dec_even : decide ((n % 10) % 2 = (0 : u64)) = true :=
          decide_eq_true h_even
        rw [h_dec_even]; simp only [↓reduceIte]
        rw [div_pure n 10 (by decide : (10 : u64) ≠ 0)]
        simp only [pure_bind]
        rw [h_e1_eq]; simp only [pure_bind]
        -- Nat-level: this is the even branch as well.
        have h_mod_nat_zero : n.toNat % 10 % 2 = 0 := by
          have h_t : ((n % 10) % 2).toNat = (0 : u64).toNat := by rw [h_even]
          rw [h_mod10_2_toNat, u64_zero_toNat] at h_t
          exact h_t
        rw [count_at_nat_succ_even n.toNat e.toNat o.toNat hn_pos h_mod_nat_zero]
        have h_new_bound : (e + 1).toNat + o.toNat + k' < 2 ^ 64 := by
          rw [h_e1_toNat]; omega
        have h_app :=
          ih (n / 10) (e + 1) o k' h_div_le_m
            (by rw [h_div10_toNat]; exact h_n_div_lt)
            h_new_bound
        rw [h_app]
        rw [h_div10_toNat, h_e1_toNat]
      · -- Odd branch.
        have h_dec_even : decide ((n % 10) % 2 = (0 : u64)) = false :=
          decide_eq_false h_even
        rw [h_dec_even]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [div_pure n 10 (by decide : (10 : u64) ≠ 0)]
        simp only [pure_bind]
        rw [h_o1_eq]; simp only [pure_bind]
        have h_mod_nat_ne : n.toNat % 10 % 2 ≠ 0 := by
          intro h_eq
          apply h_even
          apply UInt64.toNat_inj.mp
          rw [h_mod10_2_toNat, u64_zero_toNat]
          exact h_eq
        rw [count_at_nat_succ_odd n.toNat e.toNat o.toNat hn_pos h_mod_nat_ne]
        have h_new_bound : e.toNat + (o + 1).toNat + k' < 2 ^ 64 := by
          rw [h_o1_toNat]; omega
        have h_app :=
          ih (n / 10) e (o + 1) k' h_div_le_m
            (by rw [h_div10_toNat]; exact h_n_div_lt)
            h_new_bound
        rw [h_app]
        rw [h_div10_toNat, h_o1_toNat]

/-! ## Contract clauses

The Rust source carries one `known` block with five unit pins and one
proptest `matches_reference` that checks the closed-form digit-count
postcondition on every `u64`.  Each becomes one theorem below.

Feasibility note for `matches_reference`: a `u64` value has at most 20
decimal digits (since `2^64 < 10^20`), so the accumulators
`e + o ≤ 20 ≪ 2^64` and no overflow is possible. The universal
statement is therefore true in the Lean model without any precondition.
-/

/-- Unit pin from `known`: `even_odd_count(0) = (1, 0)` (the lone digit
    `0` is counted as one even digit). -/
theorem even_odd_count_at_0 :
    clever_153_even_odd_count.even_odd_count 0
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (0 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(7) = (0, 1)`. -/
theorem even_odd_count_at_7 :
    clever_153_even_odd_count.even_odd_count 7
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : u64) (1 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(12) = (1, 1)`. -/
theorem even_odd_count_at_12 :
    clever_153_even_odd_count.even_odd_count 12
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (1 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(123) = (1, 2)`. -/
theorem even_odd_count_at_123 :
    clever_153_even_odd_count.even_odd_count 123
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (2 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(246) = (3, 0)`. -/
theorem even_odd_count_at_246 :
    clever_153_even_odd_count.even_odd_count 246
      = RustM.ok (rust_primitives.hax.Tuple2.mk (3 : u64) (0 : u64)) := by
  native_decide

/-- Main postcondition (`matches_reference`): for every `u64 num`,
    `even_odd_count num` succeeds and returns the digit-by-digit even/odd
    counts of `num` (with the `n = 0` special case counting one even
    digit).  Holds universally because the digit count of any `u64` is
    at most 20, far below `2^64`. -/
theorem even_odd_count_matches_reference (num : u64) :
    clever_153_even_odd_count.even_odd_count num
      = RustM.ok (rust_primitives.hax.Tuple2.mk
          (UInt64.ofNat (even_odd_count_nat num.toNat).1)
          (UInt64.ofNat (even_odd_count_nat num.toNat).2)) := by
  unfold clever_153_even_odd_count.even_odd_count
  by_cases h_zero : num = 0
  · -- Wrapper short-circuit for `num = 0`.
    subst h_zero
    have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
      show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
      rfl
    simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
    -- `even_odd_count_nat 0 = (1, 0)` by definition.
    show RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (0 : u64))
        = RustM.ok (rust_primitives.hax.Tuple2.mk
            (UInt64.ofNat (even_odd_count_nat (0 : u64).toNat).1)
            (UInt64.ofNat (even_odd_count_nat (0 : u64).toNat).2))
    have h_oracle :
        even_odd_count_nat (0 : u64).toNat = (1, 0) := by
      rw [u64_zero_toNat]
      unfold even_odd_count_nat
      rw [if_pos rfl]
    rw [h_oracle]
    rfl
  · -- General `num ≠ 0` case: delegate to `count_at_correct`.
    rw [u64_eq_test]
    have h_dec_false : decide (num = (0 : u64)) = false := decide_eq_false h_zero
    simp only [pure_bind, h_dec_false, Bool.false_eq_true, ↓reduceIte]
    have h_num_pos : 0 < num.toNat := u64_toNat_pos_of_ne_zero num h_zero
    have h_num_ne : num.toNat ≠ 0 := Nat.pos_iff_ne_zero.mp h_num_pos
    have h_lt20 : num.toNat < 10 ^ 20 := u64_toNat_lt_pow20 num
    have h_bound : (0 : u64).toNat + (0 : u64).toNat + 20 < 2 ^ 64 := by
      rw [u64_zero_toNat]; decide
    have h_eq :=
      count_at_correct num.toNat num (0 : u64) (0 : u64) 20
        (Nat.le_refl _) h_lt20 h_bound
    rw [h_eq]
    -- `even_odd_count_nat num.toNat = count_at_nat num.toNat 0 0` (since
    -- num.toNat ≠ 0).
    have h_oracle :
        even_odd_count_nat num.toNat = count_at_nat num.toNat 0 0 := by
      unfold even_odd_count_nat
      rw [if_neg h_num_ne]
    rw [h_oracle]
    show RustM.ok (rust_primitives.hax.Tuple2.mk
            (UInt64.ofNat (count_at_nat num.toNat (0 : u64).toNat (0 : u64).toNat).1)
            (UInt64.ofNat (count_at_nat num.toNat (0 : u64).toNat (0 : u64).toNat).2))
        = RustM.ok (rust_primitives.hax.Tuple2.mk
            (UInt64.ofNat (count_at_nat num.toNat 0 0).1)
            (UInt64.ofNat (count_at_nat num.toNat 0 0).2))
    rw [u64_zero_toNat]

end Clever_153_even_odd_countObligations
