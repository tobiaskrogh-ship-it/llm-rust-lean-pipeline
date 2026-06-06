-- Companion obligations file for the `clever_035_fizz_buzz` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_035_fizz_buzz

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_035_fizz_buzzObligations

/-! ## Specification oracles on `Nat`

The Rust `reference` function transcribed at the Nat level. Used to phrase
the closed-form postcondition without mentioning `i64` arithmetic on the
spec side. Both helpers are total on `Nat`: `count_sevens_nat` decreases on
`n / 10` (which is `< n` for `n > 0`), and `fizz_buzz_scan` decreases on
`n - start`. -/

/-- Count occurrences of the digit `7` in the base-10 representation of `n`. -/
private def count_sevens_nat (n : Nat) : Nat :=
  if h : 0 < n then
    (if n % 10 = 7 then 1 else 0) + count_sevens_nat (n / 10)
  else 0
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-- Sum of digit-7 counts over indices `i ∈ [start, n)` divisible by 11 or 13.
    Mirrors the imperative `reference` function in the Rust source's
    `tests` module. -/
private def fizz_buzz_scan (n start : Nat) : Nat :=
  if h : start < n then
    (if start % 11 = 0 ∨ start % 13 = 0 then count_sevens_nat start else 0) +
      fizz_buzz_scan n (start + 1)
  else 0
termination_by n - start
decreasing_by omega

/-! ## Contract clauses

The Rust source contains three contract-style tests in `mod tests`:
  * `prop_nonpositive_returns_zero` — boundary clause `n ≤ 0 ⇒ 0`.
  * `prop_matches_reference` — main postcondition on `1 ≤ n ≤ 600`.
  * `unit_known_values` — four concrete pins at `50, 78, 79, 100`.

Each becomes one independent `theorem` below.  Per the obligations
guidelines we use equational form (`f x = RustM.ok …`) for boundary and
unit clauses, and an existential bundling totality with the closed-form
spec for the main postcondition (matching `largest_divisor`'s style). -/

/-! ## Helpers reused below. -/

private theorem i64_zero_toInt : ((0 : i64).toInt) = 0 := rfl
private theorem i64_one_toInt  : ((1 : i64).toInt) = 1 := rfl

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions, mirroring `below_zero_modified`.
    Not `@[simp]` because the implicit `α` causes norm_cast / exact_mod_cast
    to hit max recursion depth in unrelated downstream goals. -/
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- Boundary clause: for every non-positive `n`, the half-open scan range
    `[0, n)` is empty, so the result is `0`.  Captures the proptest
    `prop_nonpositive_returns_zero`. -/
theorem fizz_buzz_nonpositive_returns_zero
    (n : i64) (h : n ≤ (0 : i64)) :
    clever_035_fizz_buzz.fizz_buzz n = RustM.ok (0 : i64) := by
  show clever_035_fizz_buzz.scan_at (0 : i64) n (0 : i64) = RustM.ok (0 : i64)
  unfold clever_035_fizz_buzz.scan_at
  -- `(0 : i64) >=? n` reduces to `pure (decide (n ≤ 0))`.
  have h_dec : decide (n ≤ (0 : i64)) = true := decide_eq_true h
  simp only [show ((0 : i64) >=? n) =
               (pure (decide (n ≤ (0 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ## Helper: pointwise correctness of `count_sevens` against the Nat oracle.

Induction on the strong measure `n.toInt.toNat` (which strictly decreases via
`/? 10` for `n > 0`). The bound `v.toInt ≤ 19` follows because each recursive
step adds at most `1` and the recursion depth is bounded by the number of
decimal digits of `n`, which for any `i64` is at most 19. We weaken to
`v.toInt ≤ 20` for headroom under `+? 1`. -/

private theorem int64_min_lt : Int64.minValue.toInt = -9223372036854775808 := by
  decide

private theorem ten_ne_neg_one_i64 : (10 : i64) ≠ (-1 : i64) := by decide
private theorem ten_ne_zero_i64    : (10 : i64) ≠ (0 : i64)  := by decide
private theorem ten_pos_int        : (0 : Int) < 10           := by decide

/-- Local helper: `(x / y).toNat = x.toNat / y.toNat` for non-negative
    integers `x, y`. The core Lean library exposes `Int.toNat_emod` for
    `%`, but no analogue for `/`; we prove the latter here in the same
    shape as `toNat_emod` (case-split via `eq_ofNat_of_zero_le`). -/
private theorem int_toNat_ediv {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x / y).toNat = x.toNat / y.toNat :=
  match x, y, Int.eq_ofNat_of_zero_le hx, Int.eq_ofNat_of_zero_le hy with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

/-- Successor equation for `count_sevens_nat`, separated to avoid `unfold`
    unfolding nested recursive calls. -/
private theorem count_sevens_nat_succ_eq (n : Nat) (h : 0 < n) :
    count_sevens_nat n =
      (if n % 10 = 7 then 1 else 0) + count_sevens_nat (n / 10) := by
  conv => lhs; unfold count_sevens_nat
  rw [dif_pos h]

/-- Zero equation for `count_sevens_nat`. -/
private theorem count_sevens_nat_zero_eq (n : Nat) (h : ¬ 0 < n) :
    count_sevens_nat n = 0 := by
  unfold count_sevens_nat; rw [dif_neg h]

private theorem count_sevens_nat_le_pow (k : Nat) :
    ∀ n : Nat, n < 10 ^ k → count_sevens_nat n ≤ k := by
  induction k with
  | zero =>
    intro n h
    have hn0 : n = 0 := by simp at h; omega
    have h_cs0 : count_sevens_nat n = 0 := by
      rw [hn0]; exact count_sevens_nat_zero_eq 0 (by decide)
    omega
  | succ k ih =>
    intro n h
    by_cases hn : 0 < n
    · have h_div : n / 10 < 10 ^ k := by
        have h10 : 10 ^ (k + 1) = 10 * 10 ^ k := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [h10] at h
        exact Nat.div_lt_of_lt_mul h
      have ih_app : count_sevens_nat (n / 10) ≤ k := ih (n / 10) h_div
      rw [count_sevens_nat_succ_eq n hn]
      by_cases h7 : n % 10 = 7
      · rw [if_pos h7]; omega
      · rw [if_neg h7]; omega
    · have h_cs0 : count_sevens_nat n = 0 := count_sevens_nat_zero_eq n hn
      omega

/-- Concrete bound for `i64` inputs: any `n.toInt < 2^63 < 10^19`,
    so `count_sevens_nat n.toInt.toNat ≤ 19`. -/
private theorem count_sevens_nat_bound_i64 (n : i64) (hn : 0 ≤ n.toInt) :
    count_sevens_nat n.toInt.toNat ≤ 19 := by
  apply count_sevens_nat_le_pow 19
  have h_lt : n.toInt < 2^63 := by
    have h := Int64.toInt_lt n
    have h63 : (Int64.size : Int) / 2 = 2^63 := by decide
    omega
  have h63 : (2^63 : Int) ≤ 10^19 := by decide
  have h_lt_pow : n.toInt < 10 ^ 19 := by omega
  have hh : (n.toInt.toNat : Int) < 10^19 := by
    rw [Int.toNat_of_nonneg hn]; exact h_lt_pow
  exact_mod_cast hh

/-- Pointwise correctness of `count_sevens` against the Nat oracle:
    for any non-negative `n : i64`, `count_sevens n` succeeds with a
    value whose `toInt` equals `count_sevens_nat n.toInt.toNat`, and the
    result is bounded by 19 (at most 19 decimal digits in any i64).
    Induction on the strong measure `n.toInt.toNat`. -/
private theorem count_sevens_correct (n : i64) (hn : 0 ≤ n.toInt) :
    ∃ v : i64, clever_035_fizz_buzz.count_sevens n = RustM.ok v
      ∧ v.toInt = (count_sevens_nat n.toInt.toNat : Int)
      ∧ 0 ≤ v.toInt
      ∧ v.toInt ≤ 19 := by
  induction hk : n.toInt.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    have hn_lt_max : n.toInt < 9223372036854775808 := by
      have h := Int64.toInt_lt n
      have h63 : (Int64.size : Int) / 2 = 9223372036854775808 := by decide
      omega
    unfold clever_035_fizz_buzz.count_sevens
    by_cases hn_le_zero : n ≤ (0 : i64)
    · -- Base case: n ≤ 0 ∧ n.toInt ≥ 0 ⇒ n.toInt = 0.
      have hh : n.toInt ≤ 0 := by
        have := Int64.le_iff_toInt_le.mp hn_le_zero
        simpa [i64_zero_toInt] using this
      have hn_zero : n.toInt = 0 := by omega
      have hk_zero : k = 0 := by rw [← hk, hn_zero]; rfl
      have h_dec : decide (n ≤ (0 : i64)) = true := decide_eq_true hn_le_zero
      simp only [show (n <=? (0 : i64)) =
                   (pure (decide (n ≤ (0 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      refine ⟨0, rfl, ?_, ?_, ?_⟩
      · -- 0.toInt = count_sevens_nat k = count_sevens_nat 0 = 0
        have hcz : count_sevens_nat 0 = 0 := count_sevens_nat_zero_eq 0 (by decide)
        rw [hk_zero, hcz, i64_zero_toInt]; rfl
      · rw [i64_zero_toInt]; decide
      · rw [i64_zero_toInt]; decide
    · -- Step case: n > 0
      have hn_ne_zero : n.toInt ≠ 0 := by
        intro heq
        apply hn_le_zero
        apply Int64.le_iff_toInt_le.mpr
        rw [i64_zero_toInt, heq]
        decide
      have hn_pos : 0 < n.toInt := by omega
      have h_dec : decide (n ≤ (0 : i64)) = false := decide_eq_false hn_le_zero
      simp only [show (n <=? (0 : i64)) =
                   (pure (decide (n ≤ (0 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      have hn_ne_min : n ≠ Int64.minValue := by
        intro h
        have h' : n.toInt = Int64.minValue.toInt := by rw [h]
        rw [int64_min_lt] at h'; omega
      have h_and_mod : (n = Int64.minValue && (10 : i64) = -1) = false := by
        rcases Decidable.em (n = Int64.minValue) with hn_eq | hn_neq
        · exact absurd hn_eq hn_ne_min
        · simp [hn_neq]
      have h_rem : (n %? (10 : i64) : RustM i64) = pure (n % 10) := by
        show (rust_primitives.ops.arith.Rem.rem n (10 : i64) : RustM i64) = pure (n % 10)
        show (if n = Int64.minValue && (10 : i64) = -1 then
                (.fail .integerOverflow : RustM i64)
              else if (10 : i64) = 0 then .fail .divisionByZero
              else pure (n % 10)) = pure (n % 10)
        rw [h_and_mod, if_neg ten_ne_zero_i64]; rfl
      have h_div : (n /? (10 : i64) : RustM i64) = pure (n / 10) := by
        show (rust_primitives.ops.arith.Div.div n (10 : i64) : RustM i64) = pure (n / 10)
        show (if n = Int64.minValue && (10 : i64) = -1 then
                (.fail .integerOverflow : RustM i64)
              else if (10 : i64) = 0 then .fail .divisionByZero
              else pure (n / 10)) = pure (n / 10)
        rw [h_and_mod, if_neg ten_ne_zero_i64]; rfl
      rw [h_rem]
      simp only [pure_bind]
      have h_modInt : (n % 10).toInt = n.toInt.tmod 10 := Int64.toInt_mod n 10
      have h_modInt' : (n % 10).toInt = n.toInt % 10 := by
        rw [h_modInt, Int.tmod_eq_emod_of_nonneg hn]
      have h_divInt : (n / 10).toInt = n.toInt.tdiv 10 :=
        Int64.toInt_div_of_ne_right n 10 ten_ne_neg_one_i64
      have h_divInt' : (n / 10).toInt = n.toInt / 10 := by
        rw [h_divInt, Int.tdiv_eq_ediv_of_nonneg hn]
      have h_quot_nn : 0 ≤ (n / 10).toInt := by
        rw [h_divInt']; exact Int.ediv_nonneg hn (by decide)
      have h_quot_lt : (n / 10).toInt < n.toInt := by
        rw [h_divInt']
        exact Int.ediv_lt_self_of_pos_of_ne_one hn_pos (by decide)
      have h_measure : (n / 10).toInt.toNat < k := by
        rw [← hk]
        exact (Int.toNat_lt_toNat (by omega)).mpr h_quot_lt
      obtain ⟨v_rec, hv_eq, hv_int, hv_nn, hv_le⟩ :=
        ih (n / 10).toInt.toNat h_measure (n / 10) h_quot_nn rfl
      have h_n_toNat_pos : 0 < n.toInt.toNat := by
        have hh1 : (n.toInt.toNat : Int) > 0 := by rw [Int.toNat_of_nonneg hn]; exact hn_pos
        exact_mod_cast hh1
      -- Key cast bridge: (n / 10).toInt.toNat = n.toInt.toNat / 10
      have h_div_nat : (n / 10).toInt.toNat = n.toInt.toNat / 10 := by
        rw [h_divInt']
        exact int_toNat_ediv hn (by decide)
      have h_unfold :
          count_sevens_nat n.toInt.toNat =
            (if n.toInt.toNat % 10 = 7 then 1 else 0)
              + count_sevens_nat (n.toInt.toNat / 10) :=
        count_sevens_nat_succ_eq n.toInt.toNat h_n_toNat_pos
      -- Bridge: n.toInt.toNat % 10 = (n % 10).toInt.toNat
      have h_mod_nat : (n % 10).toInt.toNat = n.toInt.toNat % 10 := by
        rw [h_modInt']
        exact Int.toNat_emod hn (by decide)
      -- v_rec ≤ 18 (bound based on n/10 having at most 18 digits)
      have h_bound18 : count_sevens_nat (n / 10).toInt.toNat ≤ 18 := by
        rw [h_div_nat]
        apply count_sevens_nat_le_pow 18
        have h63_pow : (2 ^ 63 : Int) ≤ 10 ^ 19 := by decide
        have h_lt19 : (n.toInt.toNat : Int) < 10 ^ 19 := by
          rw [Int.toNat_of_nonneg hn]; omega
        have h_lt19_nat : n.toInt.toNat < 10 ^ 19 := by exact_mod_cast h_lt19
        have h_split : (10 ^ 19 : Nat) = 10 * 10 ^ 18 := by decide
        rw [h_split] at h_lt19_nat
        exact Nat.div_lt_of_lt_mul h_lt19_nat
      have hv_rec_le18 : v_rec.toInt ≤ 18 := by
        rw [hv_int]
        exact_mod_cast h_bound18
      by_cases h_mod7 : n % 10 = (7 : i64)
      · -- digit-7 case: returns count_sevens (n/10) + 1
        have h_dec2 : decide ((n % 10) = (7 : i64)) = true := decide_eq_true h_mod7
        simp only [show ((n % 10) ==? (7 : i64)) =
                     (pure (decide ((n % 10) = (7 : i64))) : RustM Bool) from rfl,
                   h_dec2, pure_bind, ↓reduceIte]
        rw [h_div]
        simp only [pure_bind]
        rw [hv_eq]
        simp only [RustM_ok_bind]
        have h_no_overflow : ¬ Int64.addOverflow v_rec (1 : i64) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rw [i64_one_toInt] at hov
          have h63 : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
          rw [h63] at hov
          rcases hov with hov | hov
          · omega
          · omega
        have h_add : (v_rec +? (1 : i64) : RustM i64) = pure (v_rec + 1) := by
          show (rust_primitives.ops.arith.Add.add v_rec (1 : i64) : RustM i64) = _
          show (if BitVec.saddOverflow v_rec.toBitVec ((1 : i64).toBitVec) then
                  (.fail .integerOverflow : RustM i64)
                else pure (v_rec + 1)) = pure (v_rec + 1)
          have h_no_bv : BitVec.saddOverflow v_rec.toBitVec ((1 : i64).toBitVec) = false := by
            simpa [Int64.addOverflow] using h_no_overflow
          rw [h_no_bv]; rfl
        rw [h_add]
        refine ⟨v_rec + 1, rfl, ?_, ?_, ?_⟩
        · -- Apply h_div_nat to hv_int *before* substituting it into the goal,
          -- so both sides reference n.toInt.toNat / 10 in the same form.
          rw [h_div_nat] at hv_int
          rw [Int64.toInt_add_of_not_addOverflow h_no_overflow, i64_one_toInt, hv_int]
          have h_mod7_nat : n.toInt.toNat % 10 = 7 := by
            rw [← h_mod_nat, h_mod7]
            decide
          -- Goal has count_sevens_nat k on the RHS; bridge via ← hk.
          rw [← hk]
          -- Reduce the `if` cleanly using an intermediate `have`.
          have h_unfold_pos :
              count_sevens_nat n.toInt.toNat
                = 1 + count_sevens_nat (n.toInt.toNat / 10) := by
            rw [h_unfold, if_pos h_mod7_nat]
          rw [h_unfold_pos]
          push_cast; omega
        · rw [Int64.toInt_add_of_not_addOverflow h_no_overflow, i64_one_toInt]
          omega
        · rw [Int64.toInt_add_of_not_addOverflow h_no_overflow, i64_one_toInt]
          omega
      · -- no digit-7 case: returns count_sevens (n/10)
        have h_dec2 : decide ((n % 10) = (7 : i64)) = false := decide_eq_false h_mod7
        simp only [show ((n % 10) ==? (7 : i64)) =
                     (pure (decide ((n % 10) = (7 : i64))) : RustM Bool) from rfl,
                   h_dec2, pure_bind, Bool.false_eq_true, ↓reduceIte]
        rw [h_div]
        simp only [pure_bind]
        refine ⟨v_rec, hv_eq, ?_, hv_nn, ?_⟩
        · have h_mod7_nat : n.toInt.toNat % 10 ≠ 7 := by
            intro hh
            apply h_mod7
            apply Int64.toInt_inj.mp
            show (n % 10).toInt = (7 : i64).toInt
            have h7_int : (7 : i64).toInt = 7 := by decide
            rw [h7_int]
            -- Goal: (n % 10).toInt = 7
            have hmod_nn : 0 ≤ (n % 10).toInt := by
              rw [h_modInt']
              exact Int.emod_nonneg n.toInt (by decide)
            have hh_cast : (n % 10).toInt.toNat = 7 := by rw [h_mod_nat]; exact hh
            have h_cast : ((n % 10).toInt.toNat : Int) = (n % 10).toInt :=
              Int.toNat_of_nonneg hmod_nn
            rw [← h_cast, hh_cast]; rfl
          -- Apply h_div_nat to hv_int first.
          rw [h_div_nat] at hv_int
          -- Goal: Int64.toInt v_rec = ↑(count_sevens_nat k); bridge to n.toInt.toNat.
          rw [← hk, hv_int]
          have h_unfold_neg :
              count_sevens_nat n.toInt.toNat
                = 0 + count_sevens_nat (n.toInt.toNat / 10) := by
            rw [h_unfold, if_neg h_mod7_nat]
          rw [h_unfold_neg]
          push_cast; omega
        · omega

/-! ## Bound on `fizz_buzz_scan`

For every `start, n : Nat`, the scan sums up at most `count_sevens_nat ≤ 19`
per index in `[start, n)`, giving `fizz_buzz_scan n start ≤ 19 * (n - start)`.
Used to discharge the accumulator-no-overflow precondition. -/

private theorem fizz_buzz_scan_zero_eq (n start : Nat) (h : ¬ start < n) :
    fizz_buzz_scan n start = 0 := by
  unfold fizz_buzz_scan
  rw [dif_neg h]

private theorem fizz_buzz_scan_succ_eq (n start : Nat) (h : start < n) :
    fizz_buzz_scan n start =
      (if start % 11 = 0 ∨ start % 13 = 0 then count_sevens_nat start else 0) +
        fizz_buzz_scan n (start + 1) := by
  conv => lhs; unfold fizz_buzz_scan
  rw [dif_pos h]

/-- For `n ≤ 10^19` (i.e., any `i64`-bounded value's `toInt.toNat`), every
    index `start < n` has `count_sevens_nat start ≤ 19`, so the whole scan
    is bounded by `19 * (n - start)`. -/
private theorem fizz_buzz_scan_le_19_times (n : Nat) (h_n : n ≤ 10^19) :
    ∀ start : Nat, fizz_buzz_scan n start ≤ 19 * (n - start) := by
  intro start
  induction h_m : (n - start) using Nat.strongRecOn generalizing start with
  | _ m ih =>
    by_cases h_lt : start < n
    · -- step case
      have h_succ := fizz_buzz_scan_succ_eq n start h_lt
      have h_term_lt : n - (start + 1) < m := by rw [← h_m]; omega
      have h_ih : fizz_buzz_scan n (start + 1) ≤ 19 * (n - (start + 1)) :=
        ih (n - (start + 1)) h_term_lt (start + 1) rfl
      have h_term_eq : n - start = (n - (start + 1)) + 1 := by omega
      have h_start_lt_pow : start < 10 ^ 19 := by omega
      have h_first_le : (if start % 11 = 0 ∨ start % 13 = 0 then count_sevens_nat start else 0)
                          ≤ 19 := by
        by_cases hcond : start % 11 = 0 ∨ start % 13 = 0
        · rw [if_pos hcond]
          exact count_sevens_nat_le_pow 19 start h_start_lt_pow
        · rw [if_neg hcond]; omega
      rw [h_succ]
      -- Goal: (if ...) + fizz_buzz_scan n (start + 1) ≤ 19 * m
      -- h_m : n - start = m, h_term_eq : n - start = (n - (start+1)) + 1
      -- h_first_le, h_ih provide the bounds; omega handles linear arithmetic.
      omega
    · -- base case: start ≥ n ⇒ scan returns 0
      have h_zero : fizz_buzz_scan n start = 0 := fizz_buzz_scan_zero_eq n start h_lt
      rw [h_zero]; omega

/-- Correctness of `scan_at` against the Nat oracle `fizz_buzz_scan`.
    Strong induction on the ascending measure `n.toInt.toNat - i.toInt.toNat`.
    Step case splits on `i.toInt.toNat % 11 = 0 ∨ i.toInt.toNat % 13 = 0`,
    invokes `count_sevens_correct` for the inner recursive call in the
    divisible branch, and propagates the no-overflow accumulator invariant
    via `h_fbs_succ : fizz_buzz_scan n i = count_sevens_nat i + fizz_buzz_scan n (i+1)`. -/
private theorem scan_at_correct
    (n : i64) (h_n_pos : 0 ≤ n.toInt) (h_n_le : n.toInt ≤ 600)
    (i : i64) (h_i_pos : 0 ≤ i.toInt) (h_i_le : i.toInt ≤ n.toInt)
    (acc : i64) (h_acc_pos : 0 ≤ acc.toInt)
    (h_acc_bound :
      acc.toInt + (fizz_buzz_scan n.toInt.toNat i.toInt.toNat : Int) < 2^31) :
    ∃ v : i64, clever_035_fizz_buzz.scan_at i n acc = RustM.ok v
      ∧ v.toInt = acc.toInt
                  + (fizz_buzz_scan n.toInt.toNat i.toInt.toNat : Int) := by
  -- Induction on the strong measure n.toInt.toNat - i.toInt.toNat.
  -- Note: derive i.toNat ≤ n.toNat *inside* the step, not before the induction,
  -- to avoid polluting the IH with an extra hypothesis.
  induction hm : (n.toInt.toNat - i.toInt.toNat) using Nat.strongRecOn
      generalizing i acc with
  | _ m ih =>
    unfold clever_035_fizz_buzz.scan_at
    -- Common: n ≠ minValue, i ≠ minValue, i64 bounds.
    have hn_lt_max : n.toInt < 9223372036854775808 := by
      have h := Int64.toInt_lt n
      have h63 : (Int64.size : Int) / 2 = 9223372036854775808 := by decide
      omega
    have hi_lt_max : i.toInt < 9223372036854775808 := by
      have h := Int64.toInt_lt i
      have h63 : (Int64.size : Int) / 2 = 9223372036854775808 := by decide
      omega
    by_cases h_done : n ≤ i
    · -- Base case: n ≤ i. Function returns pure acc; fizz_buzz_scan is 0.
      have h_n_le_i : n.toInt ≤ i.toInt := Int64.le_iff_toInt_le.mp h_done
      have h_n_le_i_nat : n.toInt.toNat ≤ i.toInt.toNat := by
        have h_n_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg h_n_pos
        have h_i_cast : (i.toInt.toNat : Int) = i.toInt := Int.toNat_of_nonneg h_i_pos
        have : (n.toInt.toNat : Int) ≤ (i.toInt.toNat : Int) := by
          rw [h_n_cast, h_i_cast]; exact h_n_le_i
        omega
      have h_dec : decide (n ≤ i) = true := decide_eq_true h_done
      simp only [show (i >=? n) =
                   (pure (decide (n ≤ i)) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      refine ⟨acc, rfl, ?_⟩
      have h_not_lt : ¬ i.toInt.toNat < n.toInt.toNat := by omega
      have h_scan_zero : fizz_buzz_scan n.toInt.toNat i.toInt.toNat = 0 :=
        fizz_buzz_scan_zero_eq n.toInt.toNat i.toInt.toNat h_not_lt
      rw [h_scan_zero]
      push_cast; omega
    · -- Step case: i < n.
      have h_n_not_le_i : ¬ n.toInt ≤ i.toInt := by
        intro hh
        apply h_done
        exact Int64.le_iff_toInt_le.mpr hh
      have h_i_lt_n : i.toInt < n.toInt := by omega
      have h_i_lt_n_nat : i.toInt.toNat < n.toInt.toNat := by
        have h_n_cast : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg h_n_pos
        have h_i_cast : (i.toInt.toNat : Int) = i.toInt := Int.toNat_of_nonneg h_i_pos
        have : (i.toInt.toNat : Int) < (n.toInt.toNat : Int) := by
          rw [h_i_cast, h_n_cast]; exact h_i_lt_n
        omega
      have h_dec : decide (n ≤ i) = false := decide_eq_false h_done
      simp only [show (i >=? n) =
                   (pure (decide (n ≤ i)) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      have hi_ne_min : i ≠ Int64.minValue := by
        intro h
        have h' : i.toInt = Int64.minValue.toInt := by rw [h]
        rw [int64_min_lt] at h'; omega
      -- Reduce i %? 11 and i %? 13.
      have h_and11 : (i = Int64.minValue && (11 : i64) = -1) = false := by
        rcases Decidable.em (i = Int64.minValue) with hi_eq | hi_neq
        · exact absurd hi_eq hi_ne_min
        · simp [hi_neq]
      have h_and13 : (i = Int64.minValue && (13 : i64) = -1) = false := by
        rcases Decidable.em (i = Int64.minValue) with hi_eq | hi_neq
        · exact absurd hi_eq hi_ne_min
        · simp [hi_neq]
      have h_rem11 : (i %? (11 : i64) : RustM i64) = pure (i % 11) := by
        show (rust_primitives.ops.arith.Rem.rem i (11 : i64) : RustM i64) = pure (i % 11)
        show (if i = Int64.minValue && (11 : i64) = -1 then
                (.fail .integerOverflow : RustM i64)
              else if (11 : i64) = 0 then .fail .divisionByZero
              else pure (i % 11)) = pure (i % 11)
        rw [h_and11, if_neg (by decide : (11 : i64) ≠ 0)]; rfl
      have h_rem13 : (i %? (13 : i64) : RustM i64) = pure (i % 13) := by
        show (rust_primitives.ops.arith.Rem.rem i (13 : i64) : RustM i64) = pure (i % 13)
        show (if i = Int64.minValue && (13 : i64) = -1 then
                (.fail .integerOverflow : RustM i64)
              else if (13 : i64) = 0 then .fail .divisionByZero
              else pure (i % 13)) = pure (i % 13)
        rw [h_and13, if_neg (by decide : (13 : i64) ≠ 0)]; rfl
      rw [h_rem11]
      simp only [pure_bind]
      -- Compute the boolean for (i % 11) ==? 0
      have h_mod11_int : (i % 11).toInt = i.toInt.tmod 11 := Int64.toInt_mod i 11
      have h_mod11_int' : (i % 11).toInt = i.toInt % 11 := by
        rw [h_mod11_int, Int.tmod_eq_emod_of_nonneg h_i_pos]
      have h_mod13_int : (i % 13).toInt = i.toInt.tmod 13 := Int64.toInt_mod i 13
      have h_mod13_int' : (i % 13).toInt = i.toInt % 13 := by
        rw [h_mod13_int, Int.tmod_eq_emod_of_nonneg h_i_pos]
      -- Reduce (i % 11) ==? 0 to pure (decide ((i % 11) = 0))
      rw [h_rem13]
      simp only [pure_bind]
      -- The condition `((i % 11) ==? 0) ||? ((i % 13) ==? 0)` reduces.
      -- Compute the result as a single boolean.
      have h_div_or : (decide ((i % 11) = (0 : i64)) ||
                      decide ((i % 13) = (0 : i64))) =
                     decide (i.toInt.toNat % 11 = 0 ∨ i.toInt.toNat % 13 = 0) := by
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff]
        constructor
        · rintro (h | h)
          · left
            have h1 : (i % 11).toInt = 0 := by rw [h]; decide
            have h2 : i.toInt % 11 = 0 := by rw [← h_mod11_int']; exact h1
            have h_emod : (i.toInt % 11).toNat = i.toInt.toNat % 11 :=
              Int.toNat_emod h_i_pos (by decide : (0 : Int) ≤ 11)
            omega
          · right
            have h1 : (i % 13).toInt = 0 := by rw [h]; decide
            have h2 : i.toInt % 13 = 0 := by rw [← h_mod13_int']; exact h1
            have h_emod : (i.toInt % 13).toNat = i.toInt.toNat % 13 :=
              Int.toNat_emod h_i_pos (by decide : (0 : Int) ≤ 13)
            omega
        · rintro (h | h)
          · left
            apply Int64.toInt_inj.mp
            rw [h_mod11_int']
            show i.toInt % 11 = (0 : i64).toInt
            rw [i64_zero_toInt]
            have hmod_nn : 0 ≤ i.toInt % 11 := Int.emod_nonneg i.toInt (by decide)
            have h_eq : (i.toInt % 11).toNat = i.toInt.toNat % 11 :=
              Int.toNat_emod h_i_pos (by decide : (0 : Int) ≤ 11)
            rw [h] at h_eq
            have h_cast : (i.toInt % 11) = ((i.toInt % 11).toNat : Int) :=
              (Int.toNat_of_nonneg hmod_nn).symm
            rw [h_cast, h_eq]; rfl
          · right
            apply Int64.toInt_inj.mp
            rw [h_mod13_int']
            show i.toInt % 13 = (0 : i64).toInt
            rw [i64_zero_toInt]
            have hmod_nn : 0 ≤ i.toInt % 13 := Int.emod_nonneg i.toInt (by decide)
            have h_eq : (i.toInt % 13).toNat = i.toInt.toNat % 13 :=
              Int.toNat_emod h_i_pos (by decide : (0 : Int) ≤ 13)
            rw [h] at h_eq
            have h_cast : (i.toInt % 13) = ((i.toInt % 13).toNat : Int) :=
              (Int.toNat_of_nonneg hmod_nn).symm
            rw [h_cast, h_eq]; rfl
      -- Reduce i +? 1 (no overflow since i.toInt + 1 ≤ n.toInt ≤ 600 ≤ 2^63 - 1)
      have h_no_iadd : ¬ Int64.addOverflow i (1 : i64) := by
        intro hov
        rw [Int64.addOverflow_iff] at hov
        rw [i64_one_toInt] at hov
        have h63 : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
        rw [h63] at hov
        rcases hov with hov | hov
        · omega
        · omega
      have h_add_i1 : (i +? (1 : i64) : RustM i64) = pure (i + 1) := by
        show (rust_primitives.ops.arith.Add.add i (1 : i64) : RustM i64) = _
        show (if BitVec.saddOverflow i.toBitVec ((1 : i64).toBitVec) then
                (.fail .integerOverflow : RustM i64)
              else pure (i + 1)) = pure (i + 1)
        have h_no_bv : BitVec.saddOverflow i.toBitVec ((1 : i64).toBitVec) = false := by
          simpa [Int64.addOverflow] using h_no_iadd
        rw [h_no_bv]; rfl
      have h_i1_toInt : (i + 1).toInt = i.toInt + 1 := by
        rw [Int64.toInt_add_of_not_addOverflow h_no_iadd, i64_one_toInt]
      have h_i1_toNat : (i + 1).toInt.toNat = i.toInt.toNat + 1 := by
        have h_cast : (i.toInt.toNat : Int) = i.toInt := Int.toNat_of_nonneg h_i_pos
        have : ((i + 1).toInt.toNat : Int) = (i.toInt + 1) := by
          rw [Int.toNat_of_nonneg (by rw [h_i1_toInt]; omega), h_i1_toInt]
        have h2 : ((i.toInt.toNat + 1 : Nat) : Int) = i.toInt + 1 := by
          push_cast; rw [h_cast]
        omega
      have h_i1_pos : 0 ≤ (i + 1).toInt := by rw [h_i1_toInt]; omega
      have h_i1_le_n : (i + 1).toInt ≤ n.toInt := by rw [h_i1_toInt]; omega
      have h_measure_new : n.toInt.toNat - (i + 1).toInt.toNat < m := by
        rw [← hm, h_i1_toNat]; omega
      -- Two cases: divisible or not.
      by_cases h_cond_nat : i.toInt.toNat % 11 = 0 ∨ i.toInt.toNat % 13 = 0
      · -- Divisible case: scan_at recurses with acc + count_sevens i
        have h_dec_or : decide (i.toInt.toNat % 11 = 0 ∨ i.toInt.toNat % 13 = 0) = true :=
          decide_eq_true h_cond_nat
        -- Apply the boolean reduction.
        have h_or_simpl : (decide ((i % 11) = (0 : i64)) ||
                          decide ((i % 13) = (0 : i64))) = true := by
          rw [h_div_or]; exact h_dec_or
        -- Reduce all the comparison/OR steps.
        simp only [show ((i % 11) ==? (0 : i64)) =
                     (pure (decide ((i % 11) = (0 : i64))) : RustM Bool) from rfl,
                   show ((i % 13) ==? (0 : i64)) =
                     (pure (decide ((i % 13) = (0 : i64))) : RustM Bool) from rfl,
                   show ∀ a b, (a ||? b) = pure (a || b) from
                     fun a b => rfl,
                   pure_bind, h_or_simpl, ↓reduceIte]
        -- Now apply count_sevens_correct to count_sevens i.
        obtain ⟨v_cs, hv_cs_eq, hv_cs_int, hv_cs_nn, hv_cs_le⟩ :=
          count_sevens_correct i h_i_pos
        rw [hv_cs_eq]
        simp only [RustM_ok_bind]
        -- Reduce acc +? v_cs.
        -- Need: no overflow on acc + v_cs.
        -- We have h_acc_bound : acc.toInt + fizz_buzz_scan n.toInt.toNat i.toInt.toNat < 2^31
        -- And fizz_buzz_scan n.toInt.toNat i.toInt.toNat
        --   = count_sevens_nat i.toInt.toNat + fizz_buzz_scan n.toInt.toNat (i.toInt.toNat + 1)
        --     (since i < n and divisible)
        have h_fbs_succ : fizz_buzz_scan n.toInt.toNat i.toInt.toNat =
            count_sevens_nat i.toInt.toNat
              + fizz_buzz_scan n.toInt.toNat (i.toInt.toNat + 1) := by
          have h_succ_eq := fizz_buzz_scan_succ_eq n.toInt.toNat i.toInt.toNat h_i_lt_n_nat
          rw [h_succ_eq, if_pos h_cond_nat]
        have h_v_cs_int : v_cs.toInt = (count_sevens_nat i.toInt.toNat : Int) := hv_cs_int
        have h_no_accadd : ¬ Int64.addOverflow acc v_cs := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          have h63 : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
          rw [h63] at hov
          have h_acc_lt_max : acc.toInt < 9223372036854775808 := by
            have h := Int64.toInt_lt acc
            have h63' : (Int64.size : Int) / 2 = 9223372036854775808 := by decide
            omega
          have h_2_31 : (2 : Int) ^ 31 < 9223372036854775808 := by decide
          have h_fbs_nn : (0 : Int) ≤ (fizz_buzz_scan n.toInt.toNat (i.toInt.toNat + 1) : Int) :=
            Int.natCast_nonneg _
          -- h_acc_bound, h_v_cs_int, h_fbs_succ together with hov give a contradiction.
          have h_acc_bound' : acc.toInt + (count_sevens_nat i.toInt.toNat : Int)
              + (fizz_buzz_scan n.toInt.toNat (i.toInt.toNat + 1) : Int) < 2^31 := by
            have h_succ_cast : (fizz_buzz_scan n.toInt.toNat i.toInt.toNat : Int) =
                (count_sevens_nat i.toInt.toNat : Int)
                  + (fizz_buzz_scan n.toInt.toNat (i.toInt.toNat + 1) : Int) := by
              rw [h_fbs_succ]; push_cast; omega
            rw [h_succ_cast] at h_acc_bound
            omega
          rcases hov with hov | hov
          · -- acc + v_cs ≥ 2^63
            have h_v_cs_int' : v_cs.toInt = (count_sevens_nat i.toInt.toNat : Int) := h_v_cs_int
            omega
          · omega
        have h_add_acc : (acc +? v_cs : RustM i64) = pure (acc + v_cs) := by
          show (rust_primitives.ops.arith.Add.add acc v_cs : RustM i64) = _
          show (if BitVec.saddOverflow acc.toBitVec v_cs.toBitVec then
                  (.fail .integerOverflow : RustM i64)
                else pure (acc + v_cs)) = pure (acc + v_cs)
          have h_no_bv : BitVec.saddOverflow acc.toBitVec v_cs.toBitVec = false := by
            simpa [Int64.addOverflow] using h_no_accadd
          rw [h_no_bv]; rfl
        rw [h_add_acc, h_add_i1]
        simp only [pure_bind]
        -- Now apply IH at (i+1, acc + v_cs).
        have h_acc_v_cs_toInt : (acc + v_cs).toInt = acc.toInt + v_cs.toInt :=
          Int64.toInt_add_of_not_addOverflow h_no_accadd
        have h_acc_v_cs_pos : 0 ≤ (acc + v_cs).toInt := by
          rw [h_acc_v_cs_toInt]; omega
        have h_acc_v_cs_bound : (acc + v_cs).toInt
              + (fizz_buzz_scan n.toInt.toNat (i + 1).toInt.toNat : Int) < 2^31 := by
          rw [h_acc_v_cs_toInt, h_v_cs_int, h_i1_toNat]
          rw [h_fbs_succ] at h_acc_bound
          push_cast at h_acc_bound ⊢
          omega
        obtain ⟨v, hv_eq', hv_int'⟩ :=
          ih (n.toInt.toNat - (i + 1).toInt.toNat) h_measure_new (i + 1) h_i1_pos
            h_i1_le_n (acc + v_cs) h_acc_v_cs_pos h_acc_v_cs_bound rfl
        refine ⟨v, hv_eq', ?_⟩
        rw [hv_int', h_acc_v_cs_toInt, h_v_cs_int, h_i1_toNat]
        rw [h_fbs_succ]
        push_cast; omega
      · -- Non-divisible case: scan_at recurses with same acc
        have h_dec_or : decide (i.toInt.toNat % 11 = 0 ∨ i.toInt.toNat % 13 = 0) = false :=
          decide_eq_false h_cond_nat
        have h_or_simpl : (decide ((i % 11) = (0 : i64)) ||
                          decide ((i % 13) = (0 : i64))) = false := by
          rw [h_div_or]; exact h_dec_or
        simp only [show ((i % 11) ==? (0 : i64)) =
                     (pure (decide ((i % 11) = (0 : i64))) : RustM Bool) from rfl,
                   show ((i % 13) ==? (0 : i64)) =
                     (pure (decide ((i % 13) = (0 : i64))) : RustM Bool) from rfl,
                   show ∀ a b, (a ||? b) = pure (a || b) from
                     fun a b => rfl,
                   pure_bind, h_or_simpl, Bool.false_eq_true, ↓reduceIte]
        rw [h_add_i1]
        simp only [pure_bind]
        -- fizz_buzz_scan n i = 0 + fizz_buzz_scan n (i+1) when not divisible
        have h_fbs_succ : fizz_buzz_scan n.toInt.toNat i.toInt.toNat =
            fizz_buzz_scan n.toInt.toNat (i.toInt.toNat + 1) := by
          have h_succ_eq := fizz_buzz_scan_succ_eq n.toInt.toNat i.toInt.toNat h_i_lt_n_nat
          rw [h_succ_eq, if_neg h_cond_nat]
          omega
        have h_acc_bound' : acc.toInt
              + (fizz_buzz_scan n.toInt.toNat (i + 1).toInt.toNat : Int) < 2^31 := by
          rw [h_i1_toNat, ← h_fbs_succ]; exact h_acc_bound
        obtain ⟨v, hv_eq', hv_int'⟩ :=
          ih (n.toInt.toNat - (i + 1).toInt.toNat) h_measure_new (i + 1) h_i1_pos
            h_i1_le_n acc h_acc_pos h_acc_bound' rfl
        refine ⟨v, hv_eq', ?_⟩
        rw [hv_int', h_i1_toNat, ← h_fbs_succ]

/-- Main postcondition (functional correctness): on positive inputs in the
    proptest's safe range `1 ≤ n ≤ 600`, the function succeeds and the
    returned `i64` agrees, as an integer, with the prefix-scan reference
    oracle `fizz_buzz_scan`.  The `n ≤ 600` upper bound matches the
    proptest's `n in 1i64..=600` precondition and rules out the accumulator
    overflow `acc + count_sevens i` could otherwise hit on huge inputs.
    Captures the proptest `prop_matches_reference`.

    Proved by application of `scan_at_correct` at `i = 0, acc = 0`. The
    accumulator-no-overflow precondition is discharged by
    `fizz_buzz_scan_le_19_times` (≤ 19 * 600 = 11400 < 2^31). -/
theorem fizz_buzz_matches_reference
    (n : i64) (h_pos : (1 : i64) ≤ n) (h_le : n ≤ (600 : i64)) :
    ∃ v : i64,
      clever_035_fizz_buzz.fizz_buzz n = RustM.ok v
      ∧ v.toInt = (fizz_buzz_scan n.toInt.toNat 0 : Int) := by
  have h_n_pos : (1 : Int) ≤ n.toInt := by
    have := Int64.le_iff_toInt_le.mp h_pos
    simpa [i64_one_toInt] using this
  have h_n_le : n.toInt ≤ 600 := by
    have := Int64.le_iff_toInt_le.mp h_le
    simpa using this
  have h_n_ge0 : 0 ≤ n.toInt := by omega
  -- Bound on `fizz_buzz_scan n 0`: at most 19 digit-7 hits per index in [0, n),
  -- and n ≤ 600, so the scan is ≤ 19 * 600 = 11400 < 2^31. Discharged via
  -- the `fizz_buzz_scan_le_19_times` helper.
  have h_cast_n : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg h_n_ge0
  have h_n_le_nat : n.toInt.toNat ≤ 600 := by
    have h_le_int : (n.toInt.toNat : Int) ≤ 600 := by rw [h_cast_n]; exact h_n_le
    omega
  have h_acc_bound :
      (0 : Int) + (fizz_buzz_scan n.toInt.toNat 0 : Int) < 2^31 := by
    have h_pow_19 : n.toInt.toNat ≤ 10^19 := by
      have h_600_le : (600 : Nat) ≤ 10^19 := by decide
      omega
    have h_bound := fizz_buzz_scan_le_19_times n.toInt.toNat h_pow_19 0
    -- h_bound : fizz_buzz_scan n.toInt.toNat 0 ≤ 19 * (n.toInt.toNat - 0)
    have h_19n : 19 * (n.toInt.toNat - 0) ≤ 11400 := by omega
    have h_fbs_le : fizz_buzz_scan n.toInt.toNat 0 ≤ 11400 := by omega
    -- Convert to Int and combine with 2^31 bound.
    have h_2_31 : (11400 : Int) < 2^31 := by decide
    omega
  obtain ⟨v, hv_eq, hv_int⟩ :=
    scan_at_correct n h_n_ge0 h_n_le (0 : i64) (by simp [i64_zero_toInt])
      (by simpa [i64_zero_toInt] using h_n_ge0) (0 : i64)
      (by simp [i64_zero_toInt])
      (by simpa [i64_zero_toInt] using h_acc_bound)
  refine ⟨v, ?_, ?_⟩
  · show clever_035_fizz_buzz.fizz_buzz n = RustM.ok v
    have : clever_035_fizz_buzz.fizz_buzz n
            = clever_035_fizz_buzz.scan_at (0 : i64) n (0 : i64) := rfl
    rw [this]; exact hv_eq
  · -- v.toInt = 0 + fizz_buzz_scan n.toInt.toNat (0 : i64).toInt.toNat
    rw [hv_int]
    have h_zero_toNat : ((0 : i64).toInt).toNat = 0 := by simp [i64_zero_toInt]
    rw [h_zero_toNat, i64_zero_toInt]
    simp

/-- Unit pin from `unit_known_values`: at `n = 50` no multiple of 11 or 13
    in `[0, 50)` contains the digit `7`. -/
theorem fizz_buzz_at_50 :
    clever_035_fizz_buzz.fizz_buzz (50 : i64) = RustM.ok (0 : i64) := by
  native_decide

/-- Unit pin from `unit_known_values`: `fizz_buzz 78 = 2` (digit-7
    occurrences at `i = 77` only — one `7` in each of `77`'s two digits). -/
theorem fizz_buzz_at_78 :
    clever_035_fizz_buzz.fizz_buzz (78 : i64) = RustM.ok (2 : i64) := by
  native_decide

/-- Unit pin from `unit_known_values`: `fizz_buzz 79 = 3`.  Adds the
    `i = 78`-divisor-13 hit (digit `7` at the tens place) to `fizz_buzz 78`.
    Differentiates the half-open interval `[0, n)` from `[0, n]`. -/
theorem fizz_buzz_at_79 :
    clever_035_fizz_buzz.fizz_buzz (79 : i64) = RustM.ok (3 : i64) := by
  native_decide

/-- Unit pin from `unit_known_values`: `fizz_buzz 100 = 3`.  No further
    digit-7 hits in `[79, 100)` because the multiples of 11/13 in that
    range — 88, 91, 99 — contain no `7`. -/
theorem fizz_buzz_at_100 :
    clever_035_fizz_buzz.fizz_buzz (100 : i64) = RustM.ok (3 : i64) := by
  native_decide

end Clever_035_fizz_buzzObligations
