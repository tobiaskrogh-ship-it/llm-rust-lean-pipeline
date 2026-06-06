-- Companion obligations file for the `clever_024_factorize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

/-! ## Spec-level predicates

`IsPrime` and `array_product_int` give us pure-`Int` oracles to phrase the
post-conditions without leaking machine-int overflow concerns into the spec.
Each factor returned by `factorize` is positive (and ≥ 2 because the
algorithm only ever appends primes `p ≥ 2` or a residual `n > 1`), so the
`Int`-level statements line up with the Rust tests. -/

/-- An integer is prime iff it is at least 2 and has no proper divisor
    strictly between 1 and itself. -/
private def IsPrime (x : Int) : Prop :=
  2 ≤ x ∧ ∀ m : Int, 2 ≤ m → m < x → ¬ m ∣ x

/-- Product of an `i64` array, taken in `Int` to avoid overflow concerns.
    Matches the Rust test's `factors.iter().product()` semantically when the
    true product fits in `i64` (it does for the proptest's `n ∈ 2..10^6`). -/
private def array_product_int (a : Array i64) : Int :=
  a.foldl (fun acc x => acc * x.toInt) 1

/-! ## Small Int64 reductions used throughout the file. -/

private theorem int64_toInt_zero : ((0 : i64).toInt) = 0 := rfl
private theorem int64_toInt_one : ((1 : i64).toInt) = 1 := rfl
private theorem int64_toInt_two : ((2 : i64).toInt) = 2 := rfl

/-- Push a single element onto a Vec (mirrors the `push_one` helpers in
    `rescale_to_unit_modified` / `clever_009_rolling_max_modified`). The
    extracted `factorize_at` builds output via
    `extend_from_slice (acc, unsize #v[x])`, which reduces to `acc ++ #[x]`. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Primality from trial-division frontier + sqrt-bound.

If no integer in `[2, p)` divides `n` and `p * p > n`, then `n` is prime.

The classical argument: any divisor `m` of `n` with `2 ≤ m < n` either has
`m < p` (so frontier rules it out) or `m ≥ p`. In the latter case, writing
`n = m * k`, we get `k = n / m < p` (using `p * p > n`), and `k` is also
a non-trivial divisor of `n` with `2 ≤ k < p`, contradicting frontier.

This helper is left with a focused `sorry` on the `m ≥ p` branch — purely
number-theoretic and depending only on `Int` arithmetic, no monadic
machinery. **Structural unblock**: a verified arithmetic lemma "trial
division up to √n suffices for primality", proved once in a shared
Hax-prelude addition (e.g. `MissingLean/Int/Primality.lean`), would close
the remaining branch in one line. -/
private theorem isPrime_of_frontier_and_pp_gt_n
    (n p : Int) (hn : 2 ≤ n) (hp : 2 ≤ p) (hpp : p * p > n)
    (h_front : ∀ q : Int, 2 ≤ q → q < p → ¬ q ∣ n) :
    IsPrime n := by
  refine ⟨hn, ?_⟩
  intro m hm hlt hmd
  by_cases hmp : m < p
  · exact h_front m hm hmp hmd
  · have hmp' : p ≤ m := by omega
    -- m ≥ p, m ∣ n: write n = m * k for the complementary divisor k.
    obtain ⟨k, hnk⟩ := hmd
    have hm_pos : 0 < m := by omega
    have hp_pos : 0 < p := by omega
    have hn_pos : 0 < n := by omega
    -- k > 0: from n = m * k, m > 0, n > 0. We rule out k ≤ 0 by cases.
    have hk_pos : 0 < k := by
      apply Decidable.byContradiction
      intro hk_npos
      have hk_le : k ≤ 0 := Int.not_lt.mp hk_npos
      by_cases hk_eq : k = 0
      · -- k = 0 ⇒ n = 0
        rw [hk_eq, Int.mul_zero] at hnk
        omega
      · -- k < 0 ⇒ m * k < 0, but m * k = n > 0
        have hk_neg : k < 0 := by omega
        have h1 : m * k < 0 := Int.mul_neg_of_pos_of_neg hm_pos hk_neg
        rw [← hnk] at h1
        omega
    -- k < p: else m * k ≥ p * p > n, contradicting n = m * k.
    have hk_lt_p : k < p := by
      apply Decidable.byContradiction
      intro hkp
      have hkp' : p ≤ k := Int.not_lt.mp hkp
      have hp_nn : (0 : Int) ≤ p := by omega
      have hm_nn : (0 : Int) ≤ m := by omega
      have h1 : p * p ≤ m * p :=
        Int.mul_le_mul_of_nonneg_right hmp' hp_nn
      have h2 : m * p ≤ m * k :=
        Int.mul_le_mul_of_nonneg_left hkp' hm_nn
      have h3 : p * p ≤ m * k := Int.le_trans h1 h2
      rw [← hnk] at h3
      omega
    -- k ≠ 1: else n = m, contradicting m < n.
    have hk_ne_1 : k ≠ 1 := by
      intro h1
      rw [h1, Int.mul_one] at hnk
      omega
    have hk_ge_2 : 2 ≤ k := by omega
    -- k ∣ n: from n = m * k, so k * m = n, i.e. k ∣ n.
    have hk_dvd : k ∣ n := ⟨m, by rw [hnk, Int.mul_comm]⟩
    -- Apply frontier at k.
    exact h_front k hk_ge_2 hk_lt_p hk_dvd

/-! ## Overflow-discharge helpers for the recursive branches.

These lemmas establish that under the algorithmic envelope
`p.toInt ≤ n.toInt ≤ 2^31 - 1`, each of the four partial `i64`
operations used in `factorize_at` (`p *? p`, `p +? 1`, `n %? p`,
`n /? p`) is total. They are exactly the overflow-free facts the
three inner branches need on every step. -/

/-- `p * p` doesn't overflow when `p ≤ 2^31 - 1` (and ≥ 0). The product
    is at most `(2^31 - 1)^2 < 2^62 < 2^63`. -/
private theorem p_mul_p_no_overflow (p : i64)
    (h_p_nn : (0 : Int) ≤ p.toInt)
    (h_p_ub : p.toInt ≤ 2^31 - 1) :
    ¬ Int64.mulOverflow p p := by
  rw [Int64.mulOverflow_iff]
  intro h
  have h_pp_nn : (0 : Int) ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  rcases h with h_ge | h_lt
  · -- p² ≥ 2^63 is impossible since p ≤ 2^31 - 1
    have h_step1 : p.toInt * p.toInt ≤ (2^31 - 1) * p.toInt :=
      Int.mul_le_mul_of_nonneg_right h_p_ub h_p_nn
    have h_step2 : (2^31 - 1) * p.toInt ≤ (2^31 - 1) * (2^31 - 1) :=
      Int.mul_le_mul_of_nonneg_left h_p_ub (by omega : (0:Int) ≤ 2^31 - 1)
    have h_bound : p.toInt * p.toInt ≤ (2^31 - 1) * (2^31 - 1) :=
      Int.le_trans h_step1 h_step2
    have h_const : (2^31 - 1 : Int) * (2^31 - 1) < (2 : Int)^(64 - 1) := by decide
    omega
  · -- p² < -2^63 is impossible since p² ≥ 0
    have h_const : (0 : Int) ≤ (2 : Int)^(64 - 1) := by decide
    omega

/-- Reducing `p *? p` (a `RustM i64`) to a pure result, under the
    no-overflow envelope. Mirrors `largest_divisor_modified`'s `h_sub`
    block but for multiplication. -/
private theorem p_mul_p_pure (p : i64)
    (h_p_nn : (0 : Int) ≤ p.toInt)
    (h_p_ub : p.toInt ≤ 2^31 - 1) :
    (p *? p : RustM i64) = pure (p * p) := by
  show (rust_primitives.ops.arith.Mul.mul p p : RustM i64) = pure (p * p)
  show (if BitVec.smulOverflow p.toBitVec p.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (p * p)) = pure (p * p)
  have h_no_ov : ¬ Int64.mulOverflow p p := p_mul_p_no_overflow p h_p_nn h_p_ub
  have h_no_bv : BitVec.smulOverflow p.toBitVec p.toBitVec = false := by
    simpa [Int64.mulOverflow] using h_no_ov
  rw [h_no_bv]

/-! ## Bundled correctness statement for `factorize_at`

The bundled invariant carries the three independent post-conditions
(product, primality, non-decreasing) of the algorithm through every
recursive call. It is the **single** missing structural lemma in this
file — the three public obligations each derive in two-or-three lines
from it.

### Preconditions

1. `1 ≤ n.toInt` — `factorize_at` returns `acc` unchanged on `n ≤ 1`;
   we restrict to the regime where the conclusion `product v =
   product acc * n` is meaningful (it degenerates correctly at `n = 1`).
2. `2 ≤ p.toInt` — the search starts at `p = 2` and only grows.
3. `p.toInt ≤ n.toInt` — algorithmic invariant. Initially `p = 2 ≤ n`.
   After a successful divide, new `n = n_old / p ≥ p` follows from
   `p * p ≤ n_old` (since we only divide when `p² ≤ n_old`). After
   an unsuccessful trial, new `p = p_old + 1 ≤ n_old` because
   `p_old < n_old` (else `n % p = 0` would have fired).
4. `n.toInt + 1 ≤ 2^31` — overflow envelope. Guarantees `p * p`,
   `n % p`, `n / p`, `p + 1` all stay below `Int64.maxValue ≈ 2^63`.
5. `acc` invariants: every element is already prime, every element is
   `≤ p` (which together with sortedness keeps the output sorted when
   `p` is pushed next), and consecutive elements are non-decreasing.
6. `frontier`: no integer in `[2, p)` divides `n`. This is the
   propagated "search has not yet missed a prime" property — it makes
   every `p` we ever push *prime* (any divisor `q < p` of `p` would
   also divide `n`, contradicting `frontier`).

### Conclusion

The three independent post-conditions of the output Vec `v`:

* `array_product_int v = array_product_int acc * n.toInt`
* `∀ j, IsPrime v[j]`
* `∀ j, v[j] ≤ v[j+1]`

### Progress in this pass (attempt 2 of 2)

* The strong-induction skeleton is set up via `suffices aux` over the
  combined measure `n.toInt.toNat * 2^32 + (2^32 - p.toInt.toNat)`,
  which decreases strictly on both branch (b) (by ≥ 2^32, since
  `n` shrinks) and branch (c) (by exactly 1, since the `(2^32 - p)`
  term decreases). This unblocks the "missing two-parameter measure"
  issue called out in the previous attempt.
* The base case (`n ≤ 1`) is fully closed.
* The outer-if reduction in the recursive case is performed
  (`decide (n ≤ 1) = false`).
* The supporting helper `isPrime_of_frontier_and_pp_gt_n` is fully
  proved — `n` is prime when no integer in `[2, p)` divides it and
  `p² > n`. The classical small-divisor / complementary-divisor
  argument is discharged using `Int.mul_le_mul_of_nonneg_*` and
  `Int.mul_neg_of_pos_of_neg`. This kills the
  "no per-element primality reference example" gap.

### What remains stuck

The three inner branches `(p *? p > n)`, `(n %? p == 0)`, and the
fall-through. Each needs the same four ingredients (overflow-free
discharge of the partial op, decisional reduction, Vec push-step,
and — for the recursive branches — IH application with re-established
preconditions and a measure-decrease witness).

**Stuck sub-goal**: after reducing the outer `if`, the goal is

  `∃ v, factorize_at <unfolded inner body> n p acc = RustM.ok v ∧ ...`

where `<unfolded inner body>` is the three-way `if`-chain. Discharging
the `p *? p` reduction is the hardest single step — it needs a
BitVec `smulOverflow = false` proof from `p ≤ n ≤ 2^31 - 1`, mirroring
the `Int64.subOverflow` discharge in `largest_divisor_modified` but
for signed multiplication. The other reductions (`n %? p`, `n /? p`,
`p +? 1`) follow the same pattern as `largest_divisor_modified`'s
`h_rem` / `h_sub` blocks.

### Structural unblock

A single combined reference example covering `partial_fixpoint` WITH
Vec-output construction (the gap explicitly called out by the picker:
"No example combines `partial_fixpoint` *with* Vec-output construction")
would let the next pass copy the per-step structure mechanically. The
arithmetic helpers needed (primality lemma; `p² ≤ 2^62` bound from
`p ≤ 2^31`) are local and small. -/
private theorem factorize_at_correct
    (n p : i64) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_n_ge_1 : 1 ≤ n.toInt)
    (h_p_ge_2 : 2 ≤ p.toInt)
    (h_p_le_n : p.toInt ≤ n.toInt)
    (h_n_bound : n.toInt + 1 ≤ 2^31)
    (h_acc_prime : ∀ (j : Nat) (hj : j < acc.val.size),
                      IsPrime (acc.val[j]'hj).toInt)
    (h_acc_le_p : ∀ (j : Nat) (hj : j < acc.val.size),
                      (acc.val[j]'hj).toInt ≤ p.toInt)
    (h_acc_sorted : ∀ (j : Nat) (h1 : j < acc.val.size) (h2 : j+1 < acc.val.size),
                       (acc.val[j]'h1).toInt ≤ (acc.val[j+1]'h2).toInt)
    (h_frontier : ∀ q : Int, 2 ≤ q → q < p.toInt → ¬ q ∣ n.toInt) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize_at n p acc = RustM.ok v ∧
      array_product_int v.val = array_product_int acc.val * n.toInt ∧
      (∀ (j : Nat) (hj : j < v.val.size), IsPrime (v.val[j]'hj).toInt) ∧
      (∀ (j : Nat) (h1 : j < v.val.size) (h2 : j+1 < v.val.size),
         (v.val[j]'h1).toInt ≤ (v.val[j+1]'h2).toInt) := by
  -- Strong induction on combined measure
  --   `n.toInt.toNat * 2^32 + (2^32 - p.toInt.toNat)`.
  -- * Branch (b) shrinks `n.toInt` (division by `p ≥ 2`), and `p` is unchanged,
  --   so the measure drops by ≥ 2^32.
  -- * Branch (c) keeps `n.toInt` fixed and increments `p` by 1, so the
  --   `(2^32 - p)` term shrinks by 1; total measure drops by exactly 1.
  -- Both decrease strictly, enabling `Nat.strongRecOn`. Precondition
  -- `h_n_bound : n.toInt + 1 ≤ 2^31` keeps the measure inside `Nat`.
  --
  -- Repackaged as a universally-quantified auxiliary so the IH carries the
  -- preconditions (`gcd_recursive_modified`-style `induction generalizing`
  -- doesn't apply directly here because `acc` also varies on branch (b)).
  suffices aux :
    ∀ (k : Nat) (n' p' : i64) (acc' : alloc.vec.Vec i64 alloc.alloc.Global),
      n'.toInt.toNat * 2^32 + (2^32 - p'.toInt.toNat) ≤ k →
      1 ≤ n'.toInt →
      2 ≤ p'.toInt →
      p'.toInt ≤ n'.toInt →
      n'.toInt + 1 ≤ 2^31 →
      (∀ (j : Nat) (hj : j < acc'.val.size),
          IsPrime (acc'.val[j]'hj).toInt) →
      (∀ (j : Nat) (hj : j < acc'.val.size),
          (acc'.val[j]'hj).toInt ≤ p'.toInt) →
      (∀ (j : Nat) (h1 : j < acc'.val.size) (h2 : j+1 < acc'.val.size),
          (acc'.val[j]'h1).toInt ≤ (acc'.val[j+1]'h2).toInt) →
      (∀ q : Int, 2 ≤ q → q < p'.toInt → ¬ q ∣ n'.toInt) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_024_factorize.factorize_at n' p' acc' = RustM.ok v ∧
        array_product_int v.val = array_product_int acc'.val * n'.toInt ∧
        (∀ (j : Nat) (hj : j < v.val.size), IsPrime (v.val[j]'hj).toInt) ∧
        (∀ (j : Nat) (h1 : j < v.val.size) (h2 : j+1 < v.val.size),
            (v.val[j]'h1).toInt ≤ (v.val[j+1]'h2).toInt) by
    exact aux _ n p acc (Nat.le_refl _) h_n_ge_1 h_p_ge_2 h_p_le_n h_n_bound
              h_acc_prime h_acc_le_p h_acc_sorted h_frontier
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro n p acc h_meas h_n_ge_1 h_p_ge_2 h_p_le_n h_n_bound
          h_acc_prime h_acc_le_p h_acc_sorted h_frontier
    unfold clever_024_factorize.factorize_at
    by_cases h_n_le_1 : n ≤ (1 : i64)
    · -- BASE CASE: n ≤ 1 combined with h_n_ge_1 forces n.toInt = 1.
      have h_n_eq_1 : n.toInt = 1 := by
        have hh := Int64.le_iff_toInt_le.mp h_n_le_1
        rw [int64_toInt_one] at hh; omega
      have h_dec : decide (n ≤ (1 : i64)) = true := decide_eq_true h_n_le_1
      simp only [show (n <=? (1 : i64)) =
                   (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      refine ⟨acc, rfl, ?_, h_acc_prime, h_acc_sorted⟩
      rw [h_n_eq_1, Int.mul_one]
    · -- RECURSIVE CASE: n > 1. Reduce the outer `if`.
      have h_n_gt_1 : 1 < n.toInt := by
        have hh : ¬ n.toInt ≤ (1 : i64).toInt := by
          intro hle
          apply h_n_le_1
          exact Int64.le_iff_toInt_le.mpr hle
        rw [int64_toInt_one] at hh
        omega
      have h_dec_le_1 : decide (n ≤ (1 : i64)) = false := decide_eq_false h_n_le_1
      simp only [show (n <=? (1 : i64)) =
                   (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
                 h_dec_le_1, pure_bind, Bool.false_eq_true, ↓reduceIte]
      -- The three inner branches `(p *? p > n)`, `(n %? p == 0)`, and the
      -- fall-through. Each requires its own discharge — see below.
      --
      -- STUCK SUB-GOAL (post-induction, all three branches):
      -- Each branch needs four ingredients:
      -- (1) Overflow-free reduction of the relevant `i64` partial op
      --     (`p *? p`, `n %? p`, `n /? p`, `p +? 1`). The `p *? p` discharge
      --     is the hardest: `p.toInt² < 2^62 < 2^63` follows from
      --     `p ≤ n ≤ 2^31 - 1`, but needs a BitVec `smulOverflow = false`
      --     proof. The other three are direct from the
      --     `Int64.subOverflow`-style handler in `largest_divisor_modified`.
      -- (2) Vec push-step for the typed `extend_from_slice #v[x]` chunk
      --     (mirrors `rolling_max_at_step` / `shift_at_step`'s
      --     `push_one`-based discharge — see the `push_one` def above).
      -- (3) Branch-specific decisional reduction (`decide (... > n) = ?`,
      --     `decide (... = 0) = ?`).
      -- (4) For recursive branches: discharge new measure < k,
      --     re-establish all preconditions (`acc_prime`, `acc_le_p`,
      --     `acc_sorted`, `frontier`) for the recursive call's
      --     (n', p', acc'), then apply `ih`.
      --
      -- Branch (a) `p*p > n`: needs (1)+(2)+(3) AND a primality proof for
      -- `n` itself, supplied by the helper `isPrime_of_frontier_and_pp_gt_n`
      -- above (which itself carries one focused `sorry`).
      --
      -- Branch (b) `n%p = 0`: needs (1)+(2)+(3)+(4); the recursive call's
      -- frontier hypothesis re-uses `h_frontier` (p is unchanged); the
      -- primality of `p` needs `isPrime_of_frontier_and_pp_gt_n` applied
      -- with the SAME `p` (which works because `p² ≤ n` is the negation of
      -- the previous branch — but stating that requires the branch-(a)
      -- discriminant).
      --
      -- Branch (c) `n%p ≠ 0`: needs (1)+(4); the recursive call's frontier
      -- hypothesis must EXTEND `h_frontier` from `[2, p)` to `[2, p+1)`
      -- using the just-failed `n % p ≠ 0` test.
      --
      -- Structural unblock: a verified library example covering
      -- `partial_fixpoint` WITH Vec-output construction (combining
      -- `gcd_recursive_modified`'s strong-recursion pattern with
      -- `rolling_max`'s step lemma — neither single example covers both)
      -- would give the next pass a copyable template for all three
      -- branches.
      sorry

/-! ## Bridge: `factorize n` reduces to `factorize_at n 2 emptyVec`.

For `2 ≤ n` the outer `if n ≤ 1` branch is false, and the `← Impl.new`
binding reduces to the empty Vec. Pure unfolding + `decide_eq_false`. -/

private theorem factorize_eq_factorize_at
    (n : i64) (h : (2 : i64) ≤ n) :
    clever_024_factorize.factorize n =
      clever_024_factorize.factorize_at n (2 : i64)
        ⟨(List.nil : List i64).toArray, by grind⟩ := by
  unfold clever_024_factorize.factorize
  have h_not_le : ¬ n ≤ (1 : i64) := by
    intro hle
    have h1 := Int64.le_iff_toInt_le.mp hle
    have h2 := Int64.le_iff_toInt_le.mp h
    rw [int64_toInt_one] at h1
    rw [int64_toInt_two] at h2
    omega
  have h_dec : decide (n ≤ (1 : i64)) = false := decide_eq_false h_not_le
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## Bundled `factorize`-level postcondition, derived from the helper. -/

private theorem factorize_bundle
    (n : i64) (h : (2 : i64) ≤ n) (hbound : n.toInt + 1 ≤ 2^31) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      array_product_int v.val = n.toInt ∧
      (∀ (j : Nat) (hj : j < v.val.size), IsPrime (v.val[j]'hj).toInt) ∧
      (∀ (j : Nat) (h1 : j < v.val.size) (h2 : j+1 < v.val.size),
         (v.val[j]'h1).toInt ≤ (v.val[j+1]'h2).toInt) := by
  rw [factorize_eq_factorize_at n h]
  -- Now: ∃ v, factorize_at n 2 ⟨[], _⟩ = ok v ∧ ...
  have h_n_ge_2 : 2 ≤ n.toInt := by
    have := Int64.le_iff_toInt_le.mp h
    rw [int64_toInt_two] at this; exact this
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = 0 := rfl
  have h_acc0_prime :
      ∀ (j : Nat) (hj : j < acc0.val.size), IsPrime (acc0.val[j]'hj).toInt := by
    intro j hj; exfalso; rw [h_acc0_size] at hj; omega
  have h_acc0_le_p :
      ∀ (j : Nat) (hj : j < acc0.val.size), (acc0.val[j]'hj).toInt ≤ (2 : i64).toInt := by
    intro j hj; exfalso; rw [h_acc0_size] at hj; omega
  have h_acc0_sorted :
      ∀ (j : Nat) (h1 : j < acc0.val.size) (h2 : j+1 < acc0.val.size),
        (acc0.val[j]'h1).toInt ≤ (acc0.val[j+1]'h2).toInt := by
    intro j h1 h2; exfalso; rw [h_acc0_size] at h1; omega
  have h_frontier :
      ∀ q : Int, 2 ≤ q → q < (2 : i64).toInt → ¬ q ∣ n.toInt := by
    intro q hq1 hq2
    rw [int64_toInt_two] at hq2
    omega
  have h_p_ge_2 : 2 ≤ (2 : i64).toInt := by rw [int64_toInt_two]; omega
  have h_p_le_n : (2 : i64).toInt ≤ n.toInt := by rw [int64_toInt_two]; exact h_n_ge_2
  have h_n_ge_1 : 1 ≤ n.toInt := by omega
  obtain ⟨v, hres, hprod, hprime, hsorted⟩ :=
    factorize_at_correct n (2 : i64) acc0
      h_n_ge_1 h_p_ge_2 h_p_le_n hbound
      h_acc0_prime h_acc0_le_p h_acc0_sorted h_frontier
  refine ⟨v, hres, ?_, hprime, hsorted⟩
  -- array_product_int v.val = n.toInt
  -- We have: array_product_int v.val = array_product_int acc0.val * n.toInt
  -- array_product_int acc0.val = 1 (empty fold)
  have h_acc0_prod : array_product_int acc0.val = 1 := by
    show ((List.nil : List i64).toArray.foldl (fun acc x => acc * x.toInt) 1) = 1
    rfl
  rw [hprod, h_acc0_prod]
  omega

/-! ## Contract clauses

Four independent obligations, one per property test in the Rust source:

  * `empty_for_n_le_one`        — failure / edge case: `n ≤ 1` ⇒ empty Vec
  * `product_of_factors_equals_n` — post (1/3): ∏ factors = n
  * `every_factor_is_prime`       — post (2/3): each factor is prime
  * `factors_non_decreasing`      — post (3/3): factors sorted ascending

For the three post-conditions we adopt the conservative valid-regime
`2 ≤ n` precondition plus an `n.toInt + 1 ≤ 2^31` overflow envelope
(the obligations stage explicitly invited a tighter bound to discharge
`p *? p`; the proptest range `n ∈ 2..10^6` sits far below this). The
statements remain well-typed and capture the contract. -/

/-- Edge case (proptest `empty_for_n_le_one`): for any `n ≤ 1` the function
    returns successfully with an empty `Vec`. -/
theorem empty_for_n_le_one
    (n : i64) (h : n ≤ (1 : i64)) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧ v.val.size = 0 := by
  unfold clever_024_factorize.factorize
  have h_dec : decide (n ≤ (1 : i64)) = true := decide_eq_true h
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  exact ⟨⟨(List.nil : List i64).toArray, by grind⟩, rfl, rfl⟩

/-- Postcondition (1/3) — product (proptest `product_of_factors_equals_n`):
    the product of the returned factors equals `n`.

    Strengthened with the `n.toInt + 1 ≤ 2^31` overflow envelope (the
    obligations stage explicitly invited a tighter bound). Reduces in two
    lines to `factorize_bundle`, which in turn rests on
    `factorize_at_correct` — the structural-unblock docstring on that
    helper details the missing infrastructure. -/
theorem product_of_factors_equals_n
    (n : i64) (h : (2 : i64) ≤ n) (hbound : n.toInt + 1 ≤ 2^31) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      array_product_int v.val = n.toInt := by
  obtain ⟨v, hres, hprod, _, _⟩ := factorize_bundle n h hbound
  exact ⟨v, hres, hprod⟩

/-- Postcondition (2/3) — primality (proptest `every_factor_is_prime`):
    every element of the returned `Vec` is prime.

    Strengthened with the `n.toInt + 1 ≤ 2^31` overflow envelope. Two-line
    consumer of `factorize_bundle` — see structural-unblock docstring on
    `factorize_at_correct`. -/
theorem every_factor_is_prime
    (n : i64) (h : (2 : i64) ≤ n) (hbound : n.toInt + 1 ≤ 2^31) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      ∀ (j : Nat) (hj : j < v.val.size), IsPrime ((v.val[j]'hj).toInt) := by
  obtain ⟨v, hres, _, hprime, _⟩ := factorize_bundle n h hbound
  exact ⟨v, hres, hprime⟩

/-- Postcondition (3/3) — ordering (proptest `factors_non_decreasing`):
    consecutive elements are in non-decreasing order.

    Strengthened with the `n.toInt + 1 ≤ 2^31` overflow envelope. Two-line
    consumer of `factorize_bundle` — see structural-unblock docstring on
    `factorize_at_correct`. -/
theorem factors_non_decreasing
    (n : i64) (h : (2 : i64) ≤ n) (hbound : n.toInt + 1 ≤ 2^31) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_024_factorize.factorize n = RustM.ok v ∧
      ∀ (j : Nat) (h₁ : j < v.val.size) (h₂ : j + 1 < v.val.size),
        (v.val[j]'h₁).toInt ≤ (v.val[j+1]'h₂).toInt := by
  obtain ⟨v, hres, _, _, hsorted⟩ := factorize_bundle n h hbound
  exact ⟨v, hres, hsorted⟩

end Clever_024_factorizeObligations
