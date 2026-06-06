-- Companion obligations file for the `clever_024_factorize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_024_factorize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_024_factorizeObligations

/-! ## Helper definitions for the contract.

These are the mathematical counterparts of the Rust property tests.

* `factor_product v` is the (integer) product of the elements of the output
  vector. This is the spec-side analogue of the Rust test's
  `factors.iter().product()`.

* `is_prime_int p` is the standard mathematical primality predicate, stated
  over `Int` (the codomain of `Int64.toInt`). Pattern mirrors
  `is_prime_nat` from `clever_038_prime_fib_modified`. -/

/-- Integer product of the entries of the output `Vec`. -/
private def factor_product (v : alloc.vec.Vec i64 alloc.alloc.Global) : Int :=
  (v.val.toList.map (·.toInt)).foldr (· * ·) 1

/-- Mathematical primality on `Int`. -/
private def is_prime_int (p : Int) : Prop :=
  2 ≤ p ∧ ∀ k : Int, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Contract clauses

The Rust source contains four contract-style tests in `mod tests`:

  * `empty_for_n_le_one`            — failure/edge clause: `factorize` returns
                                      an empty `Vec` whenever `n ≤ 1`.
  * `product_of_factors_equals_n`   — postcondition 1: the product of the
                                      returned factors equals `n`.
  * `every_factor_is_prime`         — postcondition 2: every returned factor
                                      is prime.
  * `factors_non_decreasing`        — postcondition 3: factors are returned
                                      in non-decreasing order.

The reference `is_prime` helper in the Rust test module is *not* a contract
clause; it is the test oracle for clause 2, and is captured here as
`is_prime_int` on the spec side.

Note on the precondition for the three positive postconditions.

The proptest restricts `n ∈ [2, 1_000_000)`; the Lean model permits any
`i64`. For very large `n` close to `i64::MAX`, the trial-division loop
must reach `p ≈ ⌈√n⌉ + 1`, at which point `p *? p` overflows `i64`
(`i64::MAX ≈ 9.22·10^18` while `(⌈√(2^63)⌉ + 1)² ≈ 2^63 + 2^32 > i64::MAX`),
so the universal totality statement is false in the Lean model. The
strongest *true* common precondition is "`p² ≤ i64::MAX` for the maximum
`p` reached", which is implied by `n.toInt < 2^62`: then
`p ≤ ⌈√n⌉ + 1 ≤ 2^31 + 1`, so `p * p ≤ 2^62 + 2^32 + 1 < 2^63`. We use
this bound on the three positive clauses; it is strictly weaker than the
proptest's `n < 10^6` and matches the safety reasoning of
`is_prime_modified`'s `n.toNat < 2^32`. -/

/-! ## Numeric helper lemmas (i64 ⇄ Int bridges). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide
private theorem i64_two_toInt : (2 : i64).toInt = 2 := by decide
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_neg_one_toInt : (-1 : i64).toInt = -1 := by decide

private theorem i64_min_toInt : Int64.minValue.toInt = -(2^63 : Int) := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x
  simpa using h

private theorem i64_toInt_ge (x : i64) : -(2^63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x
  simpa using h

private theorem i64_ne_min_of_toInt_gt (x : i64) (h : -(2^63 : Int) < x.toInt) :
    x ≠ Int64.minValue := by
  intro h_eq
  rw [h_eq, i64_min_toInt] at h
  omega

private theorem i64_ne_neg_one_of_toInt_ne (x : i64) (h : x.toInt ≠ -1) :
    x ≠ (-1 : i64) := by
  intro h_eq
  rw [h_eq, i64_neg_one_toInt] at h
  exact h rfl

private theorem i64_ne_zero_of_toInt_pos (x : i64) (h : 0 < x.toInt) :
    x ≠ (0 : i64) := by
  intro h_eq
  rw [h_eq, i64_zero_toInt] at h
  omega

/-- `p *? p = pure (p * p)` when `p.toInt * p.toInt` fits in `i64`. -/
private theorem mul_self_pure (p : i64) (hnn : 0 ≤ p.toInt)
    (h : p.toInt * p.toInt < 2 ^ 63) :
    (p *? p : RustM i64) = pure (p * p) := by
  show (rust_primitives.ops.arith.Mul.mul p p : RustM i64) = pure (p * p)
  show (if BitVec.smulOverflow p.toBitVec p.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (p * p)) = _
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg hnn hnn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_bv : BitVec.smulOverflow p.toBitVec p.toBitVec = false := by
    cases hb : BitVec.smulOverflow p.toBitVec p.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  rw [h_bv]; rfl

/-- `p +? 1 = pure (p + 1)` when `p + 1` fits in `i64`. -/
private theorem add_one_pure (p : i64) (h : p.toInt + 1 < 2 ^ 63) :
    (p +? (1 : i64) : RustM i64) = pure (p + 1) := by
  show (rust_primitives.ops.arith.Add.add p 1 : RustM i64) = pure (p + 1)
  show (if BitVec.saddOverflow p.toBitVec (1 : i64).toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (p + 1)) = _
  have h_ge_min := i64_toInt_ge p
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no : ¬ Int64.addOverflow p 1 := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_bv : BitVec.saddOverflow p.toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow p.toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  rw [h_bv]; rfl

/-- `n %? p = pure (n % p)` when `0 < p.toInt` and `n ≠ minValue`. -/
private theorem mod_pure (n p : i64) (hp_pos : 0 < p.toInt) :
    (n %? p : RustM i64) = pure (n % p) := by
  show (rust_primitives.ops.arith.Rem.rem n p : RustM i64) = pure (n % p)
  show (if n = Int64.minValue && p = -1 then
          (.fail .integerOverflow : RustM i64)
        else if p = 0 then .fail .divisionByZero
        else pure (n % p)) = pure (n % p)
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have hp_ne_zero : p ≠ (0 : i64) := by
    intro h_eq
    have : p.toInt = 0 := by rw [h_eq, i64_zero_toInt]
    omega
  have h_and : (n = Int64.minValue && p = -1) = false := by
    rcases Decidable.em (n = Int64.minValue) with hn | hn
    · simp [hn, hp_ne_neg_one]
    · simp [hn]
  rw [h_and, if_neg hp_ne_zero]
  rfl

/-- `n /? p = pure (n / p)` when `0 < p.toInt` and `n ≠ minValue`. -/
private theorem div_pure (n p : i64) (hp_pos : 0 < p.toInt) :
    (n /? p : RustM i64) = pure (n / p) := by
  show (rust_primitives.ops.arith.Div.div n p : RustM i64) = pure (n / p)
  show (if n = Int64.minValue && p = -1 then
          (.fail .integerOverflow : RustM i64)
        else if p = 0 then .fail .divisionByZero
        else pure (n / p)) = pure (n / p)
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have hp_ne_zero : p ≠ (0 : i64) := by
    intro h_eq
    have : p.toInt = 0 := by rw [h_eq, i64_zero_toInt]
    omega
  have h_and : (n = Int64.minValue && p = -1) = false := by
    rcases Decidable.em (n = Int64.minValue) with hn | hn
    · simp [hn, hp_ne_neg_one]
    · simp [hn]
  rw [h_and, if_neg hp_ne_zero]
  rfl

/-- For nonneg n and pos p: `(n % p).toInt = n.toInt % p.toInt`. -/
private theorem toInt_mod_of_nonneg (n p : i64)
    (hn : 0 ≤ n.toInt) (hp : 0 < p.toInt) :
    (n % p).toInt = n.toInt % p.toInt := by
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have h_tmod : (n % p).toInt = n.toInt.tmod p.toInt :=
    Int64.toInt_mod n p
  rw [h_tmod, Int.tmod_eq_emod_of_nonneg hn]

/-- For nonneg n and pos p: `(n / p).toInt = n.toInt / p.toInt`. -/
private theorem toInt_div_of_nonneg (n p : i64)
    (hn : 0 ≤ n.toInt) (hp : 0 < p.toInt) :
    (n / p).toInt = n.toInt / p.toInt := by
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have h_tdiv : (n / p).toInt = n.toInt.tdiv p.toInt :=
    Int64.toInt_div_of_ne_right n p hp_ne_neg_one
  rw [h_tdiv, Int.tdiv_eq_ediv_of_nonneg hn]

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Reductions for the four branches of `factorize_at`.

Mirrors `count_at_*` / `has_divisor_at_unfold` in the references: each
lemma rewrites `factorize_at n p acc` according to the branch its
hypotheses select. The branches are mutually exclusive on
`n ≤ 1 / p*p > n / n % p = 0 / n % p ≠ 0`. -/

/-- `n ≤ 1` branch: returns `acc`. -/
private theorem factorize_at_n_le_one (n p : i64) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h : n.toInt ≤ 1) :
    clever_024_factorize.factorize_at n p acc = RustM.ok acc := by
  conv => lhs; unfold clever_024_factorize.factorize_at
  have h_le : n ≤ (1 : i64) := by
    apply Int64.le_iff_toInt_le.mpr
    rw [i64_one_toInt]; exact h
  have h_dec : decide (n ≤ (1 : i64)) = true := decide_eq_true h_le
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- `p*p > n` branch (with `n > 1` and `0 ≤ p`, `0 ≤ n`, and `p*p` fits):
    returns `acc` with `n` appended. -/
private theorem factorize_at_pp_gt_n (n p : i64) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_n_gt : 1 < n.toInt) (h_p_nn : 0 ≤ p.toInt)
    (h_pp_fits : p.toInt * p.toInt < 2 ^ 63)
    (h_pp_gt_n : p.toInt * p.toInt > n.toInt)
    (h_acc_size : acc.val.size + 1 < USize64.size) :
    clever_024_factorize.factorize_at n p acc =
      RustM.ok (push_one acc n h_acc_size) := by
  conv => lhs; unfold clever_024_factorize.factorize_at
  have h_not_le : ¬ n ≤ (1 : i64) := by
    intro hle
    have : n.toInt ≤ ((1 : i64).toInt) := Int64.le_iff_toInt_le.mp hle
    rw [i64_one_toInt] at this; omega
  have h_dec_le : decide (n ≤ (1 : i64)) = false := decide_eq_false h_not_le
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec_le, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mul_self_pure p h_p_nn h_pp_fits]
  simp only [pure_bind]
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no_mul : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_pp_toInt : (p * p).toInt = p.toInt * p.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul
  have h_gt_u : (p * p) > n := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [h_pp_toInt]; exact h_pp_gt_n
  have h_dec_gt : decide ((p * p) > n) = true := decide_eq_true h_gt_u
  simp only [show ((p * p) >? n : RustM Bool) =
               (pure (decide ((p * p) > n)) : RustM Bool) from rfl,
             h_dec_gt, pure_bind, ↓reduceIte]
  -- Now we need to reduce unsize and extend_from_slice
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[n] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[n], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[n] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc_size
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[n], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc n h_acc_size) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  rfl

/-- `n % p = 0` branch (with `n > 1, p > 0`, `p² ≤ n`, no overflow on p+1):
    appends `p` and recurses on `(n / p, p, acc)`. -/
private theorem factorize_at_dvd_step (n p : i64) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_n_gt : 1 < n.toInt) (h_n_nn : 0 ≤ n.toInt)
    (h_p_pos : 0 < p.toInt) (h_pp_fits : p.toInt * p.toInt < 2 ^ 63)
    (h_pp_le_n : p.toInt * p.toInt ≤ n.toInt)
    (h_dvd : p.toInt ∣ n.toInt)
    (h_acc_size : acc.val.size + 1 < USize64.size) :
    clever_024_factorize.factorize_at n p acc =
      clever_024_factorize.factorize_at (n / p) p (push_one acc p h_acc_size) := by
  conv => lhs; unfold clever_024_factorize.factorize_at
  have h_not_le : ¬ n ≤ (1 : i64) := by
    intro hle
    have : n.toInt ≤ ((1 : i64).toInt) := Int64.le_iff_toInt_le.mp hle
    rw [i64_one_toInt] at this; omega
  have h_dec_le : decide (n ≤ (1 : i64)) = false := decide_eq_false h_not_le
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec_le, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mul_self_pure p (by omega) h_pp_fits]
  simp only [pure_bind]
  have h_p_nn : 0 ≤ p.toInt := by omega
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no_mul : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_pp_toInt : (p * p).toInt = p.toInt * p.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul
  have h_not_gt : ¬ (p * p) > n := by
    intro hgt
    have : (p * p).toInt > n.toInt := Int64.lt_iff_toInt_lt.mp hgt
    rw [h_pp_toInt] at this; omega
  have h_dec_gt : decide ((p * p) > n) = false := decide_eq_false h_not_gt
  simp only [show ((p * p) >? n : RustM Bool) =
               (pure (decide ((p * p) > n)) : RustM Bool) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mod_pure n p h_p_pos]
  simp only [pure_bind]
  have h_mod_toInt : (n % p).toInt = 0 := by
    rw [toInt_mod_of_nonneg n p h_n_nn h_p_pos]
    exact Int.emod_eq_zero_of_dvd h_dvd
  have h_mod_zero : (n % p) = (0 : i64) := by
    apply Int64.toInt_inj.mp
    rw [h_mod_toInt, i64_zero_toInt]
  have h_dec_eq : decide ((n % p) = (0 : i64)) = true := decide_eq_true h_mod_zero
  simp only [show ((n % p) ==? (0 : i64) : RustM Bool) =
               (pure (decide ((n % p) = (0 : i64))) : RustM Bool) from rfl,
             h_dec_eq, pure_bind, ↓reduceIte]
  -- Reduce unsize and extend_from_slice for the [p] chunk
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[p] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[p], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[p] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc_size
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[p], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc p h_acc_size) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [div_pure n p h_p_pos]
  simp only [pure_bind]

/-- `n % p ≠ 0` branch (with `n > 1, p > 0`, `p² ≤ n`, no overflow on p+1):
    recurses on `(n, p + 1, acc)`. -/
private theorem factorize_at_nondvd_step (n p : i64) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_n_gt : 1 < n.toInt) (h_n_nn : 0 ≤ n.toInt)
    (h_p_pos : 0 < p.toInt) (h_pp_fits : p.toInt * p.toInt < 2 ^ 63)
    (h_pp_le_n : p.toInt * p.toInt ≤ n.toInt)
    (h_not_dvd : ¬ p.toInt ∣ n.toInt)
    (h_p_plus_one_fits : p.toInt + 1 < 2 ^ 63) :
    clever_024_factorize.factorize_at n p acc =
      clever_024_factorize.factorize_at n (p + 1) acc := by
  conv => lhs; unfold clever_024_factorize.factorize_at
  have h_not_le : ¬ n ≤ (1 : i64) := by
    intro hle
    have : n.toInt ≤ ((1 : i64).toInt) := Int64.le_iff_toInt_le.mp hle
    rw [i64_one_toInt] at this; omega
  have h_dec_le : decide (n ≤ (1 : i64)) = false := decide_eq_false h_not_le
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec_le, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mul_self_pure p (by omega) h_pp_fits]
  simp only [pure_bind]
  have h_p_nn : 0 ≤ p.toInt := by omega
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no_mul : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_pp_toInt : (p * p).toInt = p.toInt * p.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul
  have h_not_gt : ¬ (p * p) > n := by
    intro hgt
    have : (p * p).toInt > n.toInt := Int64.lt_iff_toInt_lt.mp hgt
    rw [h_pp_toInt] at this; omega
  have h_dec_gt : decide ((p * p) > n) = false := decide_eq_false h_not_gt
  simp only [show ((p * p) >? n : RustM Bool) =
               (pure (decide ((p * p) > n)) : RustM Bool) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mod_pure n p h_p_pos]
  simp only [pure_bind]
  have h_mod_toInt : (n % p).toInt = n.toInt % p.toInt :=
    toInt_mod_of_nonneg n p h_n_nn h_p_pos
  have h_mod_not_zero : (n % p) ≠ (0 : i64) := by
    intro h_eq
    have h_mod_i : (n % p).toInt = ((0 : i64).toInt) := by rw [h_eq]
    rw [h_mod_toInt, i64_zero_toInt] at h_mod_i
    exact h_not_dvd (Int.dvd_of_emod_eq_zero h_mod_i)
  have h_dec_eq : decide ((n % p) = (0 : i64)) = false := decide_eq_false h_mod_not_zero
  simp only [show ((n % p) ==? (0 : i64) : RustM Bool) =
               (pure (decide ((n % p) = (0 : i64))) : RustM Bool) from rfl,
             h_dec_eq, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [add_one_pure p h_p_plus_one_fits]
  simp only [pure_bind]

/-! ## Primality from trial-division.

For `n ≥ 2`: if no `k ∈ [2, p)` divides `n` and `p² > n`, then `n` is prime
(in the sense of `is_prime_int`). Standard "smallest factor ≤ √n" argument. -/

private theorem is_prime_of_no_small_divisor (n : Int) (p : Int)
    (hn : 2 ≤ n) (hp : 0 ≤ p)
    (h_no_small : ∀ d : Int, 2 ≤ d → d < p → ¬ d ∣ n)
    (h_pp_gt : p * p > n) :
    is_prime_int n := by
  refine ⟨hn, ?_⟩
  intro k hk_ge hk_lt h_dvd
  obtain ⟨d, hd⟩ := h_dvd
  -- d > 0:
  have h_n_pos : 0 < n := by omega
  have h_k_pos : 0 < k := by omega
  have h_d_pos : 0 < d := by
    rcases Decidable.em (0 < d) with h | h
    · exact h
    · exfalso
      have h_d_le : d ≤ 0 := by omega
      have h_kd_nonpos : k * d ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h_d_le
      rw [← hd] at h_kd_nonpos
      omega
  -- d ≥ 2:
  have h_d_ge_2 : 2 ≤ d := by
    rcases Decidable.em (2 ≤ d) with h | h
    · exact h
    · exfalso
      have h_d_le_1 : d ≤ 1 := by omega
      have h_d_eq_1 : d = 1 := by omega
      rw [h_d_eq_1, Int.mul_one] at hd
      omega
  -- Either k ≤ d or d < k. Take m = the smaller one; both work as witness.
  rcases Decidable.em (k ≤ d) with hkd | hkd
  · -- k ≤ d. Use m := k. k * k ≤ k * d = n, so k < p; also k | n.
    have h_kk_le_kd : k * k ≤ k * d :=
      Int.mul_le_mul_of_nonneg_left hkd (by omega)
    have h_kk_le_n : k * k ≤ n := by rw [hd]; exact h_kk_le_kd
    have h_k_lt_p : k < p := by
      rcases Decidable.em (k < p) with h | h
      · exact h
      · exfalso
        have h_p_le_k : p ≤ k := by omega
        have : p * p ≤ k * k :=
          Int.mul_le_mul h_p_le_k h_p_le_k hp (by omega)
        omega
    exact h_no_small k hk_ge h_k_lt_p ⟨d, hd⟩
  · -- d < k. Use m := d. d * d ≤ d * k = k * d = n; d ∈ [2, p); d | n.
    have h_d_lt_k : d < k := by omega
    have h_dd_le_kd : d * d ≤ k * d := by
      have : d * d ≤ k * d :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      exact this
    have h_dd_le_n : d * d ≤ n := by rw [hd]; exact h_dd_le_kd
    have h_d_lt_p : d < p := by
      rcases Decidable.em (d < p) with h | h
      · exact h
      · exfalso
        have h_p_le_d : p ≤ d := by omega
        have : p * p ≤ d * d :=
          Int.mul_le_mul h_p_le_d h_p_le_d hp (by omega)
        omega
    have h_d_dvd : d ∣ n := by
      refine ⟨k, ?_⟩
      rw [hd, Int.mul_comm]
    exact h_no_small d h_d_ge_2 h_d_lt_p h_d_dvd

/-! ## Main correctness lemma for `factorize_at`.

By strong induction on the combined measure `n.toInt.toNat + (2^33 - p.toInt.toNat)`.
This measure strictly decreases in both recursive branches:
* `n%p=0` branch: `n → n/p` strictly decreases (`p ≥ 2`); `p` unchanged.
* `n%p≠0` branch: `p → p+1` strictly increases; `n` unchanged.

The bound `p ≤ 2^31 + 1` is preserved by the recursion (we only ever call
`factorize_at` with `p+1` from the `p² ≤ n` branch, where `p² ≤ n < 2^62`
gives `p ≤ 2^31`, so `p+1 ≤ 2^31 + 1`).

The `h_no_small` precondition says: no integer in `[2, p)` divides `n`.
This is the inductive invariant — initially trivially satisfied at `p = 2`,
and preserved across both recursive branches. -/

/-- The "size-bound preserved across one push" arithmetic.
    Given `p ≥ 2`, `n ≥ 2`, `p | n`, we have `(n/p).toNat + 1 ≤ n.toNat`,
    so `(acc_size + 1) + (n/p).toNat ≤ acc_size + n.toNat`. -/
private theorem acc_size_bound_after_div
    (acc_size : Nat) (n p : Int)
    (h_n_lo : 2 ≤ n) (h_p_lo : 2 ≤ p) (h_dvd : p ∣ n)
    (h_acc : acc_size + n.toNat < USize64.size) :
    (acc_size + 1) + (n / p).toNat < USize64.size := by
  have h_n_nn : 0 ≤ n := by omega
  have h_p_pos : 0 < p := by omega
  have h_np_nn : 0 ≤ n / p := Int.ediv_nonneg h_n_nn (by omega)
  -- 2 * (n/p) ≤ p * (n/p) = n
  have h_p_np_eq_n : p * (n / p) = n := by
    obtain ⟨q, hq⟩ := h_dvd
    rw [hq, Int.mul_ediv_cancel_left q (by omega : p ≠ 0)]
  have h_2np_le_n : 2 * (n / p) ≤ n := by
    have h1 : 2 * (n / p) ≤ p * (n / p) :=
      Int.mul_le_mul_of_nonneg_right h_p_lo h_np_nn
    omega
  -- Lift to Nat: 2 * (n/p).toNat ≤ n.toNat
  have h_n_eq : (n.toNat : Int) = n := Int.toNat_of_nonneg h_n_nn
  have h_np_eq : ((n / p).toNat : Int) = n / p := Int.toNat_of_nonneg h_np_nn
  have h_2np_nat : 2 * (n / p).toNat ≤ n.toNat := by
    have h_cast : ((2 * (n / p).toNat : Nat) : Int) = 2 * (n / p) := by
      push_cast
      have := h_np_eq
      omega
    have h_int_le : ((2 * (n / p).toNat : Nat) : Int) ≤ ((n.toNat : Nat) : Int) := by
      rw [h_cast, h_n_eq]; exact h_2np_le_n
    exact_mod_cast h_int_le
  -- Also need n.toNat ≥ 2
  have h_n_ge_2_nat : 2 ≤ n.toNat := by
    have : (2 : Int) ≤ (n.toNat : Int) := by rw [h_n_eq]; exact h_n_lo
    exact_mod_cast this
  omega

private theorem factorize_at_correct
    (n p : i64) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_n_lo : 1 ≤ n.toInt) (h_n_hi : n.toInt < 2 ^ 62)
    (h_p_lo : 2 ≤ p.toInt) (h_p_hi : p.toInt ≤ 2 ^ 31 + 1)
    (h_no_small : ∀ d : Int, 2 ≤ d → d < p.toInt → ¬ d ∣ n.toInt)
    (h_acc_size : acc.val.size + n.toInt.toNat < USize64.size) :
    ∃ (v : alloc.vec.Vec i64 alloc.alloc.Global) (rest : List i64),
      clever_024_factorize.factorize_at n p acc = RustM.ok v ∧
      v.val.toList = acc.val.toList ++ rest ∧
      (∀ x ∈ rest, is_prime_int x.toInt) ∧
      rest.Pairwise (fun a b => a.toInt ≤ b.toInt) ∧
      (∀ x ∈ rest, p.toInt ≤ x.toInt) ∧
      (rest.map (·.toInt)).foldr (· * ·) 1 = n.toInt := by
  induction h_meas : (n.toInt.toNat + (2 ^ 33 - p.toInt.toNat))
    using Nat.strongRecOn generalizing n p acc with
  | _ m ih =>
    have h_p_nn : 0 ≤ p.toInt := by omega
    -- Compute p² safety: p² ≤ (2^31+1)² = 2^62 + 2^32 + 1 < 2^63
    have h_pp_fits : p.toInt * p.toInt < 2 ^ 63 := by
      have h1 : p.toInt * p.toInt ≤ (2^31 + 1) * p.toInt :=
        Int.mul_le_mul_of_nonneg_right h_p_hi h_p_nn
      have h2 : ((2 : Int)^31 + 1) * p.toInt ≤ (2^31 + 1) * (2^31 + 1) :=
        Int.mul_le_mul_of_nonneg_left h_p_hi (by decide)
      have h_bound : ((2 : Int)^31 + 1) * (2^31 + 1) < 2^63 := by decide
      omega
    by_cases hn1 : n.toInt ≤ 1
    · -- Base case: n ≤ 1 (so n = 1). Returns acc.
      have hn_eq_1 : n.toInt = 1 := by omega
      refine ⟨acc, [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact factorize_at_n_le_one n p acc hn1
      · simp
      · intro x hx; simp at hx
      · exact List.Pairwise.nil
      · intro x hx; simp at hx
      · simp [hn_eq_1]
    · -- n > 1: n.toInt ≥ 2
      have hn_gt : 1 < n.toInt := by omega
      have h_n_nn : 0 ≤ n.toInt := by omega
      have h_p_pos : 0 < p.toInt := by omega
      have h_n_ge_2 : 2 ≤ n.toInt := by omega
      -- bound h_n_toNat_pos: n.toInt.toNat ≥ 1
      have h_n_toNat_pos : 1 ≤ n.toInt.toNat := by
        have h_n_eq : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg h_n_nn
        have : (1 : Int) ≤ (n.toInt.toNat : Int) := by rw [h_n_eq]; omega
        exact_mod_cast this
      have h_acc_size_1 : acc.val.size + 1 < USize64.size := by omega
      by_cases hpp : p.toInt * p.toInt > n.toInt
      · -- p² > n: append [n]; n is prime
        have h_n_prime : is_prime_int n.toInt :=
          is_prime_of_no_small_divisor n.toInt p.toInt h_n_ge_2 h_p_nn h_no_small hpp
        -- n ≥ p (since n is prime, n ≥ 2, and p doesn't divide n unless n = p)
        have h_n_ge_p : p.toInt ≤ n.toInt := by
          -- If n < p: n ∈ [2, p), n | n (trivially), contradicts h_no_small n.
          rcases Decidable.em (n.toInt < p.toInt) with hnp | hnp
          · exfalso
            exact h_no_small n.toInt h_n_ge_2 hnp ⟨1, by simp⟩
          · omega
        refine ⟨push_one acc n h_acc_size_1, [n], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact factorize_at_pp_gt_n n p acc hn_gt h_p_nn h_pp_fits hpp h_acc_size_1
        · show (acc.val ++ #[n]).toList = acc.val.toList ++ [n]
          simp
        · intro x hx
          rcases List.mem_singleton.mp hx with rfl
          exact h_n_prime
        · exact List.pairwise_singleton _ _
        · intro x hx
          rcases List.mem_singleton.mp hx with rfl
          exact h_n_ge_p
        · simp
      · -- p² ≤ n: recurse
        have h_pp_le_n : p.toInt * p.toInt ≤ n.toInt := by omega
        -- Derive p ≤ 2^31 (so p+1 ≤ 2^31+1).
        have h_p_le : p.toInt ≤ 2 ^ 31 := by
          rcases Decidable.em (p.toInt ≤ 2^31) with h | h
          · exact h
          · exfalso
            have h_p_ge : (2 : Int)^31 + 1 ≤ p.toInt := by omega
            have h_pp_ge : ((2 : Int)^31 + 1) * (2^31 + 1) ≤ p.toInt * p.toInt :=
              Int.mul_le_mul h_p_ge h_p_ge (by decide) h_p_nn
            have h_bound : ((2 : Int)^31 + 1) * (2^31 + 1) > 2^62 := by decide
            omega
        by_cases hdvd : p.toInt ∣ n.toInt
        · -- n%p=0: push p, recurse on (n/p, p, push_one acc p).
          -- p is prime: ∀ d ∈ [2, p), ¬d | p (proven from h_no_small applied to n)
          have h_p_prime : is_prime_int p.toInt := by
            refine ⟨h_p_lo, ?_⟩
            intro k hk_ge hk_lt h_dvd_p
            -- k | p and p | n ⇒ k | n. But h_no_small k says ¬k | n.
            have h_dvd_n : k ∣ n.toInt := by
              obtain ⟨a, ha⟩ := h_dvd_p
              obtain ⟨b, hb⟩ := hdvd
              refine ⟨a * b, ?_⟩
              rw [hb, ha, Int.mul_assoc]
            exact h_no_small k hk_ge hk_lt h_dvd_n
          -- Compute (n / p).toInt
          have h_np_toInt : (n / p).toInt = n.toInt / p.toInt :=
            toInt_div_of_nonneg n p h_n_nn h_p_pos
          have h_np_lo : 1 ≤ (n / p).toInt := by
            rw [h_np_toInt]
            -- n/p ≥ 1 since p² ≤ n, p ≥ 1
            have h1 : p.toInt ≤ n.toInt / p.toInt := by
              have h_pp : p.toInt * p.toInt ≤ n.toInt := h_pp_le_n
              have : p.toInt ≤ n.toInt / p.toInt := by
                have := Int.le_ediv_iff_mul_le (a := p.toInt) (b := n.toInt) (c := p.toInt) (by omega)
                exact this.mpr h_pp
              exact this
            omega
          have h_np_hi : (n / p).toInt < 2 ^ 62 := by
            rw [h_np_toInt]
            have h1 : n.toInt / p.toInt ≤ n.toInt := by
              apply Int.ediv_le_self _ h_n_nn
            omega
          -- New h_no_small: for d ∈ [2, p), ¬ d | (n / p).
          have h_no_small_new :
              ∀ d : Int, 2 ≤ d → d < p.toInt → ¬ d ∣ (n / p).toInt := by
            intro d hd_lo hd_hi h_dvd_np
            -- d | (n/p).toInt and (n/p).toInt * p.toInt = n.toInt ⇒ d | n.toInt
            rw [h_np_toInt] at h_dvd_np
            have h_np_p_eq_n : (n.toInt / p.toInt) * p.toInt = n.toInt := by
              obtain ⟨q, hq⟩ := hdvd
              rw [hq, Int.mul_ediv_cancel_left q (by omega : p.toInt ≠ 0), Int.mul_comm]
            have h_dvd_n : d ∣ n.toInt := by
              obtain ⟨c, hc⟩ := h_dvd_np
              refine ⟨c * p.toInt, ?_⟩
              rw [← h_np_p_eq_n, hc, Int.mul_assoc]
            exact h_no_small d hd_lo hd_hi h_dvd_n
          have h_acc_size_new :
              (push_one acc p h_acc_size_1).val.size + (n / p).toInt.toNat
                < USize64.size := by
            have h_push_size : (push_one acc p h_acc_size_1).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[p]).size = _
              rw [Array.size_append]; rfl
            rw [h_push_size, h_np_toInt]
            exact acc_size_bound_after_div acc.val.size n.toInt p.toInt
              h_n_ge_2 h_p_lo hdvd h_acc_size
          -- Apply IH on (n/p, p, push_one acc p)
          have h_meas_dec :
              (n / p).toInt.toNat + (2 ^ 33 - p.toInt.toNat) < m := by
            rw [← h_meas, h_np_toInt]
            -- n/p < n (since n ≥ 2, p ≥ 2)
            have h_np_nn : 0 ≤ n.toInt / p.toInt := Int.ediv_nonneg h_n_nn (by omega)
            have h_np_lt_n_int : n.toInt / p.toInt < n.toInt := by
              -- n = p * q, n / p = q, q < p * q (since q > 0 and p > 1).
              obtain ⟨q, hq⟩ := hdvd
              have h_q_eq : n.toInt / p.toInt = q := by
                rw [hq, Int.mul_ediv_cancel_left q (by omega : p.toInt ≠ 0)]
              have h_q_pos : 0 < q := by
                rcases Decidable.em (0 < q) with h | h
                · exact h
                · exfalso
                  have h_q_le : q ≤ 0 := by omega
                  have h_neg : p.toInt * q ≤ 0 :=
                    Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h_q_le
                  rw [← hq] at h_neg; omega
              rw [h_q_eq, hq]
              -- Goal: q < p.toInt * q. From p ≥ 2 > 1 and q > 0:
              have h_one_q : 1 * q < p.toInt * q :=
                Int.mul_lt_mul_of_pos_right (by omega : (1 : Int) < p.toInt) h_q_pos
              omega
            have h_np_eq : ((n.toInt / p.toInt).toNat : Int) = n.toInt / p.toInt :=
              Int.toNat_of_nonneg h_np_nn
            have h_n_eq : (n.toInt.toNat : Int) = n.toInt := Int.toNat_of_nonneg h_n_nn
            have h_lt_lift : ((n.toInt / p.toInt).toNat : Int) < (n.toInt.toNat : Int) := by
              rw [h_np_eq, h_n_eq]; exact h_np_lt_n_int
            have h_np_lt : (n.toInt / p.toInt).toNat < n.toInt.toNat := by
              exact_mod_cast h_lt_lift
            omega
          obtain ⟨v, rest, hres, hval, hprime, hpw, hge, hprod⟩ :=
            ih _ h_meas_dec (n / p) p (push_one acc p h_acc_size_1)
              h_np_lo h_np_hi h_p_lo h_p_hi h_no_small_new h_acc_size_new rfl
          refine ⟨v, p :: rest, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- factorize_at_dvd_step then IH
            rw [factorize_at_dvd_step n p acc hn_gt h_n_nn h_p_pos h_pp_fits h_pp_le_n hdvd h_acc_size_1]
            exact hres
          · rw [hval]
            show (acc.val ++ #[p]).toList ++ rest = acc.val.toList ++ (p :: rest)
            simp
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hxr
            · exact h_p_prime
            · exact hprime x hxr
          · refine List.Pairwise.cons ?_ hpw
            intro y hy
            -- p ≤ y for y ∈ rest (which contains divisors of (n/p) all ≥ p)
            exact hge y hy
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hxr
            · exact Int.le_refl _
            · exact hge x hxr
          · -- Product: p * (rest product) = p * (n/p) = n
            simp
            -- Goal: p.toInt * (rest.map ·.toInt).foldr (· * ·) 1 = n.toInt
            rw [hprod, h_np_toInt]
            -- p * (n/p) = n
            obtain ⟨q, hq⟩ := hdvd
            rw [hq]
            have : p.toInt * q / p.toInt = q := Int.mul_ediv_cancel_left q (by omega)
            rw [this]
        · -- n%p ≠ 0: recurse on (n, p+1, acc)
          -- p+1 ≤ 2^31 + 1 (from p ≤ 2^31)
          have h_p_plus_one_fits : p.toInt + 1 < 2 ^ 63 := by omega
          -- (p+1).toInt = p.toInt + 1
          have h_p1_no_ov : ¬ Int64.addOverflow p 1 := by
            intro hov
            rw [Int64.addOverflow_iff, i64_one_toInt] at hov
            have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
            rcases hov with hov | hov
            · rw [h63] at hov
              have h_ge_min := i64_toInt_ge p
              omega
            · rw [h63] at hov
              have h_ge_min := i64_toInt_ge p
              omega
          have h_p1_toInt : (p + 1).toInt = p.toInt + 1 := by
            rw [Int64.toInt_add_of_not_addOverflow h_p1_no_ov, i64_one_toInt]
          have h_p1_lo : 2 ≤ (p + 1).toInt := by rw [h_p1_toInt]; omega
          have h_p1_hi : (p + 1).toInt ≤ 2 ^ 31 + 1 := by rw [h_p1_toInt]; omega
          -- New h_no_small: for d ∈ [2, p+1), ¬d | n
          have h_no_small_new : ∀ d : Int, 2 ≤ d → d < (p + 1).toInt → ¬ d ∣ n.toInt := by
            intro d hd_lo hd_hi h_dvd
            rw [h_p1_toInt] at hd_hi
            rcases Decidable.em (d < p.toInt) with h | h
            · exact h_no_small d hd_lo h h_dvd
            · have h_d_eq_p : d = p.toInt := by omega
              rw [h_d_eq_p] at h_dvd
              exact hdvd h_dvd
          have h_meas_dec :
              n.toInt.toNat + (2 ^ 33 - (p + 1).toInt.toNat) < m := by
            rw [← h_meas, h_p1_toInt]
            -- (p+1).toNat = p.toNat + 1
            have h_p_eq : (p.toInt.toNat : Int) = p.toInt := Int.toNat_of_nonneg h_p_nn
            have h_p1_nn : 0 ≤ p.toInt + 1 := by omega
            have h_p1_eq : ((p.toInt + 1).toNat : Int) = p.toInt + 1 :=
              Int.toNat_of_nonneg h_p1_nn
            have h_p1_succ : (p.toInt + 1).toNat = p.toInt.toNat + 1 := by
              have h_lift : ((p.toInt + 1).toNat : Int) = (p.toInt.toNat + 1 : Nat) := by
                push_cast; rw [h_p1_eq, h_p_eq]
              exact_mod_cast h_lift
            rw [h_p1_succ]
            -- We need: n.toNat + (2^33 - (p.toNat + 1)) < n.toNat + (2^33 - p.toNat)
            -- iff (2^33 - p.toNat - 1) < (2^33 - p.toNat) iff p.toNat + 1 ≤ 2^33
            have h_p_lt_233 : p.toInt.toNat + 1 ≤ 2 ^ 33 := by
              have : p.toInt ≤ 2^31 + 1 := h_p_hi
              have h_p_lift : (p.toInt.toNat : Int) ≤ 2^31 + 1 := by
                rw [h_p_eq]; exact this
              have h_p_nat_le : p.toInt.toNat ≤ 2 ^ 31 + 1 := by exact_mod_cast h_p_lift
              have h_pow : (2 : Nat) ^ 31 + 1 + 1 ≤ 2 ^ 33 := by decide
              omega
            omega
          obtain ⟨v, rest, hres, hval, hprime, hpw, hge, hprod⟩ :=
            ih _ h_meas_dec n (p + 1) acc h_n_lo h_n_hi h_p1_lo h_p1_hi h_no_small_new h_acc_size rfl
          refine ⟨v, rest, ?_, hval, hprime, hpw, ?_, hprod⟩
          · rw [factorize_at_nondvd_step n p acc hn_gt h_n_nn h_p_pos h_pp_fits h_pp_le_n hdvd h_p_plus_one_fits]
            exact hres
          · -- Each x in rest ≥ p+1 ≥ p
            intro x hx
            have := hge x hx
            rw [h_p1_toInt] at this
            omega

/-! ## Top-level invariants used to instantiate `factorize_at_correct`. -/

private theorem factorize_to_factorize_at
    (n : i64) (h_lo : 2 ≤ n.toInt) :
    clever_024_factorize.factorize n =
      clever_024_factorize.factorize_at n 2
        ⟨(List.nil : List i64).toArray, by grind⟩ := by
  unfold clever_024_factorize.factorize
  have h_n_gt_1 : ¬ n ≤ (1 : i64) := by
    intro hle
    have : n.toInt ≤ ((1 : i64).toInt) := Int64.le_iff_toInt_le.mp hle
    rw [i64_one_toInt] at this; omega
  have h_dec : decide (n ≤ (1 : i64)) = false := decide_eq_false h_n_gt_1
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_new_eq :
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk
         : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok ⟨(List.nil : List i64).toArray, by grind⟩ := rfl
  rw [h_new_eq]
  simp only [RustM_ok_bind]

/-- Empty acc has size 0 and `n.toInt.toNat < 2^62`. -/
private theorem h_acc_size_at_start (n : i64) (h_hi : n.toInt < 2 ^ 62)
    (h_lo : 0 ≤ n.toInt) :
    (⟨(List.nil : List i64).toArray, by grind⟩
      : alloc.vec.Vec i64 alloc.alloc.Global).val.size + n.toInt.toNat
        < USize64.size := by
  show 0 + n.toInt.toNat < USize64.size
  have h_usize : USize64.size = 2 ^ 64 := by decide
  rw [h_usize]
  have h_lift : n.toInt.toNat < 2 ^ 62 := by
    have : (2 : Int) ^ 62 = ((2 ^ 62 : Nat) : Int) := by decide
    rw [this] at h_hi
    have h_nat_lt : (n.toInt.toNat : Int) < ((2 ^ 62 : Nat) : Int) := by
      rw [Int.toNat_of_nonneg h_lo]; exact h_hi
    exact_mod_cast h_nat_lt
  have h_pow : (2 : Nat) ^ 62 < 2 ^ 64 := by decide
  omega

/-- Helper: from `acc = []` and `v.val.toList = [] ++ rest`. -/
private theorem rest_from_empty_acc
    (v : alloc.vec.Vec i64 alloc.alloc.Global) (rest : List i64)
    (h : v.val.toList = (⟨(List.nil : List i64).toArray, by grind⟩
            : alloc.vec.Vec i64 alloc.alloc.Global).val.toList ++ rest) :
    v.val.toList = rest := by
  show v.val.toList = rest
  rw [h]
  simp

/-- Failure/edge clause: for any `n ≤ 1`, `factorize n` returns an empty
    `Vec`. Captures the Rust property test `empty_for_n_le_one`. -/
theorem factorize_empty_for_n_le_one
    (n : i64) (h : n ≤ (1 : i64)) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧ v.val.size = 0 := by
  refine ⟨⟨(List.nil : List i64).toArray, by grind⟩, ?_, rfl⟩
  unfold clever_024_factorize.factorize
  have h_dec : decide (n ≤ (1 : i64)) = true := decide_eq_true h
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ## Helper: bundled application of `factorize_at_correct` at the
     top-level call site (acc = empty, p = 2). -/

private theorem factorize_call_correct
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ (v : alloc.vec.Vec i64 alloc.alloc.Global) (rest : List i64),
      clever_024_factorize.factorize n = RustM.ok v ∧
      v.val.toList = rest ∧
      (∀ x ∈ rest, is_prime_int x.toInt) ∧
      rest.Pairwise (fun a b => a.toInt ≤ b.toInt) ∧
      (rest.map (·.toInt)).foldr (· * ·) 1 = n.toInt := by
  rw [factorize_to_factorize_at n h_lo]
  have h_n_lo : 1 ≤ n.toInt := by omega
  have h_p_lo : 2 ≤ (2 : i64).toInt := by rw [i64_two_toInt]; decide
  have h_p_hi : (2 : i64).toInt ≤ 2 ^ 31 + 1 := by rw [i64_two_toInt]; decide
  have h_no_small : ∀ d : Int, 2 ≤ d → d < (2 : i64).toInt → ¬ d ∣ n.toInt := by
    intro d hd_lo hd_hi
    rw [i64_two_toInt] at hd_hi; omega
  have h_acc_size :
      (⟨(List.nil : List i64).toArray, by grind⟩
        : alloc.vec.Vec i64 alloc.alloc.Global).val.size + n.toInt.toNat
          < USize64.size :=
    h_acc_size_at_start n h_hi (by omega)
  obtain ⟨v, rest, hres, hval, hprime, hpw, _, hprod⟩ :=
    factorize_at_correct n 2 ⟨(List.nil : List i64).toArray, by grind⟩
      h_n_lo h_hi h_p_lo h_p_hi h_no_small h_acc_size
  refine ⟨v, rest, hres, ?_, hprime, hpw, hprod⟩
  exact rest_from_empty_acc v rest hval

/-- Postcondition 1 (product of factors equals `n`).

    Captures the Rust property test `product_of_factors_equals_n`. -/
theorem factorize_product_equals_n
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      factor_product v = n.toInt := by
  obtain ⟨v, rest, hres, hval, _, _, hprod⟩ :=
    factorize_call_correct n h_lo h_hi
  refine ⟨v, hres, ?_⟩
  unfold factor_product
  rw [hval]; exact hprod

/-- Postcondition 2 (every returned factor is prime).

    Captures the Rust property test `every_factor_is_prime`. -/
theorem factorize_every_factor_is_prime
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      (∀ (k : Nat) (hk : k < v.val.size),
          is_prime_int (v.val[k]'hk).toInt) := by
  obtain ⟨v, rest, hres, hval, hprime, _, _⟩ :=
    factorize_call_correct n h_lo h_hi
  -- After substituting rest := v.val.toList, hprime becomes a statement on v.val.
  subst hval
  refine ⟨v, hres, ?_⟩
  intro k hk
  apply hprime
  -- Goal: v.val[k] ∈ v.val.toList
  have h_arr_mem : v.val[k]'hk ∈ v.val := Array.getElem_mem hk
  exact Array.mem_def.mp h_arr_mem

/-- Postcondition 3 (factors returned in non-decreasing order).

    Captures the Rust property test `factors_non_decreasing`. Stated on
    consecutive entries, matching the test's `windows(2)` form. -/
theorem factorize_factors_non_decreasing
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      (∀ (k : Nat) (hk : k + 1 < v.val.size),
          (v.val[k]'(Nat.lt_of_succ_lt hk)).toInt
            ≤ (v.val[k + 1]'hk).toInt) := by
  obtain ⟨v, rest, hres, hval, _, hpw, _⟩ :=
    factorize_call_correct n h_lo h_hi
  subst hval
  refine ⟨v, hres, ?_⟩
  intro k hk
  -- Bridge v.val.size ↔ v.val.toList.length via simp.
  have hk1_list : k + 1 < v.val.toList.length := by simp [hk]
  have hk_list : k < v.val.toList.length := Nat.lt_of_succ_lt hk1_list
  exact List.pairwise_iff_getElem.mp hpw k (k + 1) hk_list hk1_list (Nat.lt_succ_self _)

end Clever_024_factorizeObligations
