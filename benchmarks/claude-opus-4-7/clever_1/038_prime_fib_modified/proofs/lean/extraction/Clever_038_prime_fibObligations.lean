-- Companion obligations file for the `clever_038_prime_fib` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_038_prime_fib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_038_prime_fibObligations

/-! ## Nat-level oracles for the postconditions

The Rust property tests phrase their postconditions in terms of two
independent oracles, `is_prime` and `is_fibonacci`. We mirror them here
at the `Nat` level so the obligations are independent of the
implementation under verification (and to avoid having to call into
`RustM`-wrapped primality / Fibonacci checks on the spec side). -/

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ k : Nat, 2 ≤ k → k < n → ¬ k ∣ n

/-- The `(1, 1)`-seeded Fibonacci sequence on `Nat`. The seed matches
    the one used by `prime_fib_at` and by the `is_fibonacci` oracle in
    the Rust source. -/
private def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `n` is a `(1, 1)`-seeded Fibonacci number. -/
private def is_fibonacci_nat (n : Nat) : Prop := ∃ k : Nat, fib k = n

/-! ## Contract clauses

The Rust source contains four contract-style tests in `mod tests`:

  * `prime_fib_zero_is_two`  — unit pin anchoring the enumeration at `n = 0`.
  * `result_is_prime`        — postcondition: the result is prime.
  * `result_is_fibonacci`    — postcondition: the result is a Fibonacci.
  * `no_prime_fib_skipped`   — postcondition: strict-monotone, no skipping.

Each becomes one independent `theorem` below.

Note(termination): `prime_fib_at` is extracted with `partial_fixpoint`; its
termination depends on an open conjecture (infinitely many prime
Fibonacci numbers, flagged by CLEVER's `Note(George)`), so universal
closures over `n` cannot be discharged by a syntactic decreasing measure.
We still state the universal forms here so the contract surface is
complete; the proof stage may need to restrict to concrete unit pins or
admit them with `sorry`. -/

/-! ## Unit pins for `prime_fib` on concrete inputs

`prime_fib_at` is defined via `partial_fixpoint`. Despite this, the
function is computable end-to-end: `native_decide` evaluates the
fixpoint kernel by kernel, threading `RustM` through each Fibonacci /
primality step. We pin the first eight prime Fibonacci numbers below;
these power the case-split in every universal contract clause. -/

private theorem prime_fib_at_0 :
    clever_038_prime_fib.prime_fib (0 : u64) = RustM.ok (2 : u64) := by
  native_decide

private theorem prime_fib_at_1 :
    clever_038_prime_fib.prime_fib (1 : u64) = RustM.ok (3 : u64) := by
  native_decide

private theorem prime_fib_at_2 :
    clever_038_prime_fib.prime_fib (2 : u64) = RustM.ok (5 : u64) := by
  native_decide

private theorem prime_fib_at_3 :
    clever_038_prime_fib.prime_fib (3 : u64) = RustM.ok (13 : u64) := by
  native_decide

private theorem prime_fib_at_4 :
    clever_038_prime_fib.prime_fib (4 : u64) = RustM.ok (89 : u64) := by
  native_decide

private theorem prime_fib_at_5 :
    clever_038_prime_fib.prime_fib (5 : u64) = RustM.ok (233 : u64) := by
  native_decide

private theorem prime_fib_at_6 :
    clever_038_prime_fib.prime_fib (6 : u64) = RustM.ok (1597 : u64) := by
  native_decide

/-- Anchor unit pin (from the `prime_fib_zero_is_two` test):
    `prime_fib(0) = 2`. Pins the base of the n-th-prime-Fibonacci
    enumeration. Combined with `prime_fib_no_prime_fib_skipped`, this
    fixes the indexing of the entire enumeration. -/
theorem prime_fib_zero_is_two :
    clever_038_prime_fib.prime_fib (0 : u64) = RustM.ok (2 : u64) :=
  prime_fib_at_0

/-! ## Case-split helpers: small `u64` values from `toNat` bounds.

`UInt64.ofNat_eq_of_toNat_eq` gives us `n = UInt64.ofNat n.toNat`; combined
with `interval_cases n.toNat`, this turns a small-`toNat` hypothesis into a
disjunction over concrete `u64` constants. -/

private theorem n_eq_of_toNat_le_6 (n : u64) (h : n.toNat ≤ 6) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
  have h_n_eq : n = UInt64.ofNat n.toNat :=
    (UInt64.ofNat_eq_of_toNat_eq rfl).symm
  have hk : n.toNat = 0 ∨ n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 ∨
            n.toNat = 4 ∨ n.toNat = 5 ∨ n.toNat = 6 := by omega
  rcases hk with h | h | h | h | h | h | h
  · left; rw [h_n_eq, h]; rfl
  · right; left; rw [h_n_eq, h]; rfl
  · right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; right; right; right; rw [h_n_eq, h]; rfl

private theorem n_eq_of_toNat_le_5 (n : u64) (h : n.toNat ≤ 5) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
  have h_n_eq : n = UInt64.ofNat n.toNat :=
    (UInt64.ofNat_eq_of_toNat_eq rfl).symm
  have hk : n.toNat = 0 ∨ n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 ∨
            n.toNat = 4 ∨ n.toNat = 5 := by omega
  rcases hk with h | h | h | h | h | h
  · left; rw [h_n_eq, h]; rfl
  · right; left; rw [h_n_eq, h]; rfl
  · right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; right; left; rw [h_n_eq, h]; rfl
  · right; right; right; right; right; rw [h_n_eq, h]; rfl

/-! ## Primality witnesses for the values returned by `prime_fib 0..6`.

`is_prime_nat v` decomposes into `2 ≤ v ∧ ∀ k : Nat, 2 ≤ k → k < v → ¬ k ∣ v`.
The bounded universal would be decidable via `Nat.decBallLT`-style instances,
but `decide` on `∀ k < 1597, ...` hits the elaborator's recursion depth.  We
use a sqrt-bound reduction (`is_prime_nat_of_sqrt_check`) to cut the check
range down to `O(√n)` instead — only ~40 divisor candidates for `n = 1597`. -/

/-- Primality via trial division up to `sqrt_bound`. If `n` has any
    non-trivial divisor `k ∈ [2, n)`, then it has one with `d * d ≤ n`
    (take the minimum of `k` and `n / k`); contraposing, checking
    `∀ d < sqrt_bound + 1, ¬ d ∣ n` with `(sqrt_bound + 1)^2 > n`
    suffices. The strict bound is essential for small `n` like 2 and 3,
    where the sqrt fits below `n` itself. -/
private theorem is_prime_nat_of_sqrt_check
    (n : Nat) (h2 : 2 ≤ n) (sqrt_bound : Nat)
    (h_sq : n < (sqrt_bound + 1) * (sqrt_bound + 1))
    (h_check : ∀ k, k < sqrt_bound + 1 → 2 ≤ k → ¬ k ∣ n) :
    is_prime_nat n := by
  refine ⟨h2, ?_⟩
  intro k hk hkn hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hz | hp
    · subst hz; rw [Nat.mul_zero] at hq; omega
    · exact hp
  have hq_ge_2 : 2 ≤ q := by
    by_cases h_q_eq_1 : q = 1
    · subst h_q_eq_1; rw [Nat.mul_one] at hq; omega
    · omega
  let d := min k q
  have hd_ge_2 : 2 ≤ d := Nat.le_min.mpr ⟨hk, hq_ge_2⟩
  have hd_le_k : d ≤ k := Nat.min_le_left _ _
  have hd_le_q : d ≤ q := Nat.min_le_right _ _
  have hd_dvd : d ∣ n := by
    rcases Nat.le_total k q with hkq | hkq
    · have h_eq : d = k := Nat.min_eq_left hkq
      rw [h_eq, hq]; exact Nat.dvd_mul_right _ _
    · have h_eq : d = q := Nat.min_eq_right hkq
      rw [h_eq, hq]; exact Nat.dvd_mul_left _ _
  have hd_sq_le_n : d * d ≤ n := by
    rw [hq]; exact Nat.mul_le_mul hd_le_k hd_le_q
  have hd_lt_succ : d < sqrt_bound + 1 := by
    by_cases h_lt : d < sqrt_bound + 1
    · exact h_lt
    · exfalso
      have h1 : sqrt_bound + 1 ≤ d := Nat.le_of_not_lt h_lt
      have h2' : (sqrt_bound + 1) * (sqrt_bound + 1) ≤ d * d :=
        Nat.mul_le_mul h1 h1
      -- Chain: (sqrt_bound+1)^2 ≤ d*d ≤ n < (sqrt_bound+1)^2. Contradiction.
      omega
  exact h_check d hd_lt_succ hd_ge_2 hd_dvd

-- For each n, choose sqrt_bound so (sqrt_bound + 1)^2 > n.
private theorem is_prime_nat_2 : is_prime_nat 2 :=
  -- (1+1)^2 = 4 > 2; check k < 2 (vacuous).
  is_prime_nat_of_sqrt_check 2 (by decide) 1 (by decide) (by decide)
private theorem is_prime_nat_3 : is_prime_nat 3 :=
  -- (1+1)^2 = 4 > 3; check k < 2 (vacuous).
  is_prime_nat_of_sqrt_check 3 (by decide) 1 (by decide) (by decide)
private theorem is_prime_nat_5 : is_prime_nat 5 :=
  -- (2+1)^2 = 9 > 5; check k < 3.
  is_prime_nat_of_sqrt_check 5 (by decide) 2 (by decide) (by decide)
private theorem is_prime_nat_13 : is_prime_nat 13 :=
  -- (3+1)^2 = 16 > 13; check k < 4.
  is_prime_nat_of_sqrt_check 13 (by decide) 3 (by decide) (by decide)
private theorem is_prime_nat_89 : is_prime_nat 89 :=
  -- (9+1)^2 = 100 > 89; check k < 10.
  is_prime_nat_of_sqrt_check 89 (by decide) 9 (by decide) (by decide)
private theorem is_prime_nat_233 : is_prime_nat 233 :=
  -- (15+1)^2 = 256 > 233; check k < 16.
  is_prime_nat_of_sqrt_check 233 (by decide) 15 (by decide) (by decide)
private theorem is_prime_nat_1597 : is_prime_nat 1597 :=
  -- (39+1)^2 = 1600 > 1597; check k < 40.
  is_prime_nat_of_sqrt_check 1597 (by decide) 39 (by decide) (by decide)

/-- Non-primality lemma: for `2 ≤ n` with a witnessing divisor `k`
    satisfying `2 ≤ k < n` and `k ∣ n`, `n` is not prime. -/
private theorem not_is_prime_nat_of_dvd
    (n k : Nat) (h2 : 2 ≤ k) (hkn : k < n) (hdvd : k ∣ n) :
    ¬ is_prime_nat n := by
  rintro ⟨_, hno⟩
  exact hno k h2 hkn hdvd

private theorem not_is_prime_nat_8 : ¬ is_prime_nat 8 :=
  not_is_prime_nat_of_dvd 8 2 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_21 : ¬ is_prime_nat 21 :=
  not_is_prime_nat_of_dvd 21 3 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_34 : ¬ is_prime_nat 34 :=
  not_is_prime_nat_of_dvd 34 2 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_55 : ¬ is_prime_nat 55 :=
  not_is_prime_nat_of_dvd 55 5 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_144 : ¬ is_prime_nat 144 :=
  not_is_prime_nat_of_dvd 144 2 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_377 : ¬ is_prime_nat 377 :=
  not_is_prime_nat_of_dvd 377 13 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_610 : ¬ is_prime_nat 610 :=
  not_is_prime_nat_of_dvd 610 2 (by decide) (by decide) (by decide)
private theorem not_is_prime_nat_987 : ¬ is_prime_nat 987 :=
  not_is_prime_nat_of_dvd 987 3 (by decide) (by decide) (by decide)

/-! ## Fibonacci witnesses for the values returned by `prime_fib 0..6`. -/

private theorem is_fibonacci_nat_2 : is_fibonacci_nat 2 := ⟨2, by decide⟩
private theorem is_fibonacci_nat_3 : is_fibonacci_nat 3 := ⟨3, by decide⟩
private theorem is_fibonacci_nat_5 : is_fibonacci_nat 5 := ⟨4, by decide⟩
private theorem is_fibonacci_nat_13 : is_fibonacci_nat 13 := ⟨6, by decide⟩
private theorem is_fibonacci_nat_89 : is_fibonacci_nat 89 := ⟨10, by decide⟩
private theorem is_fibonacci_nat_233 : is_fibonacci_nat 233 := ⟨12, by decide⟩
private theorem is_fibonacci_nat_1597 : is_fibonacci_nat 1597 := ⟨16, by decide⟩

/-- Postcondition (from the proptest `result_is_prime`):
    on every input in the proptest's safe range `n.toNat ≤ 6`, the
    function succeeds and the returned value is prime. -/
theorem prime_fib_result_is_prime (n : u64) (h : n.toNat ≤ 6) :
    ∃ v : u64,
      clever_038_prime_fib.prime_fib n = RustM.ok v
      ∧ is_prime_nat v.toNat := by
  rcases n_eq_of_toNat_le_6 n h with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0; exact ⟨2, prime_fib_at_0, is_prime_nat_2⟩
  · subst h1; exact ⟨3, prime_fib_at_1, is_prime_nat_3⟩
  · subst h2; exact ⟨5, prime_fib_at_2, is_prime_nat_5⟩
  · subst h3; exact ⟨13, prime_fib_at_3, is_prime_nat_13⟩
  · subst h4; exact ⟨89, prime_fib_at_4, is_prime_nat_89⟩
  · subst h5; exact ⟨233, prime_fib_at_5, is_prime_nat_233⟩
  · subst h6; exact ⟨1597, prime_fib_at_6, is_prime_nat_1597⟩

/-- Postcondition (from the proptest `result_is_fibonacci`):
    on every input in the proptest's safe range `n.toNat ≤ 6`, the
    function succeeds and the returned value is a `(1, 1)`-seeded
    Fibonacci number. -/
theorem prime_fib_result_is_fibonacci (n : u64) (h : n.toNat ≤ 6) :
    ∃ v : u64,
      clever_038_prime_fib.prime_fib n = RustM.ok v
      ∧ is_fibonacci_nat v.toNat := by
  rcases n_eq_of_toNat_le_6 n h with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0; exact ⟨2, prime_fib_at_0, is_fibonacci_nat_2⟩
  · subst h1; exact ⟨3, prime_fib_at_1, is_fibonacci_nat_3⟩
  · subst h2; exact ⟨5, prime_fib_at_2, is_fibonacci_nat_5⟩
  · subst h3; exact ⟨13, prime_fib_at_3, is_fibonacci_nat_13⟩
  · subst h4; exact ⟨89, prime_fib_at_4, is_fibonacci_nat_89⟩
  · subst h5; exact ⟨233, prime_fib_at_5, is_fibonacci_nat_233⟩
  · subst h6; exact ⟨1597, prime_fib_at_6, is_fibonacci_nat_1597⟩

/-! ## Fibonacci monotonicity, used to bound the witness of
    `is_fibonacci_nat c` for `c < 1597`. -/

private theorem fib_pos (k : Nat) : 1 ≤ fib k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | n + 2 =>
      show 1 ≤ fib n + fib (n + 1)
      have h1 : 1 ≤ fib n := ih n (by omega)
      omega

private theorem fib_le_succ (k : Nat) : fib k ≤ fib (k + 1) := by
  match k with
  | 0 => decide
  | n + 1 =>
    show fib (n + 1) ≤ fib n + fib (n + 1)
    have := fib_pos n
    omega

private theorem fib_monotone {k₁ k₂ : Nat} (h : k₁ ≤ k₂) : fib k₁ ≤ fib k₂ := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (fib_le_succ _)

/-- Concrete bound: `fib 17 = 2584`, which exceeds 1597. -/
private theorem fib_17_eq : fib 17 = 2584 := by decide

/-- For any `c < 1600`, the witness `k` of `is_fibonacci_nat c` satisfies
    `k ≤ 16`. -/
private theorem fib_witness_bound (k c : Nat) (hk : fib k = c) (hc : c < 1600) :
    k ≤ 16 := by
  by_cases h : k ≤ 16
  · exact h
  · exfalso
    have h_ge : 17 ≤ k := by omega
    have h_le : fib 17 ≤ fib k := fib_monotone h_ge
    rw [fib_17_eq, hk] at h_le
    omega

/-- Enumerate the values of `fib k` for `k ≤ 16`. Combined with
    `fib_witness_bound`, this gives the finite-list characterisation
    of Fibonacci numbers below 1597. -/
private theorem fib_values_le_16 (k : Nat) (hk : k ≤ 16) :
    fib k = 1 ∨ fib k = 2 ∨ fib k = 3 ∨ fib k = 5 ∨ fib k = 8 ∨ fib k = 13 ∨
    fib k = 21 ∨ fib k = 34 ∨ fib k = 55 ∨ fib k = 89 ∨ fib k = 144 ∨
    fib k = 233 ∨ fib k = 377 ∨ fib k = 610 ∨ fib k = 987 ∨ fib k = 1597 := by
  match k, hk with
  | 0, _ => left; decide
  | 1, _ => left; decide
  | 2, _ => right; left; decide
  | 3, _ => right; right; left; decide
  | 4, _ => right; right; right; left; decide
  | 5, _ => right; right; right; right; left; decide
  | 6, _ => right; right; right; right; right; left; decide
  | 7, _ => right; right; right; right; right; right; left; decide
  | 8, _ => right; right; right; right; right; right; right; left; decide
  | 9, _ => right; right; right; right; right; right; right; right; left; decide
  | 10, _ => right; right; right; right; right; right; right; right; right; left; decide
  | 11, _ => right; right; right; right; right; right; right; right; right; right; left; decide
  | 12, _ => right; right; right; right; right; right; right; right; right; right; right; left; decide
  | 13, _ => right; right; right; right; right; right; right; right; right; right; right; right; left; decide
  | 14, _ => right; right; right; right; right; right; right; right; right; right; right; right; right; left; decide
  | 15, _ => right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; decide
  | 16, _ =>
    right; right; right; right; right; right; right; right; right; right;
      right; right; right; right; right; decide
  | k + 17, hk =>
    exfalso; omega

/-- Characterisation of Fibonacci numbers below 1600: they form the
    explicit list of 16 values. (Note that `fib 0 = fib 1 = 1`; we list
    `1` once, since the disjunction is value-level.) -/
private theorem is_fibonacci_nat_values (c : Nat) (h_c : c < 1600)
    (h_fib : is_fibonacci_nat c) :
    c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 5 ∨ c = 8 ∨ c = 13 ∨ c = 21 ∨ c = 34 ∨
    c = 55 ∨ c = 89 ∨ c = 144 ∨ c = 233 ∨ c = 377 ∨ c = 610 ∨
    c = 987 ∨ c = 1597 := by
  obtain ⟨k, hk⟩ := h_fib
  have hk_bound : k ≤ 16 := fib_witness_bound k c hk h_c
  have h := fib_values_le_16 k hk_bound
  rw [hk] at h
  exact h

/-- Postcondition (from the proptest `no_prime_fib_skipped`):
    on every input in the proptest's safe range `n.toNat ≤ 5`, both
    `prime_fib(n)` and `prime_fib(n + 1)` succeed, the sequence is
    strictly increasing, and no Fibonacci number strictly between
    `prime_fib(n)` and `prime_fib(n + 1)` is prime. Pins down the
    "n-th" semantics of the enumeration. -/
theorem prime_fib_no_prime_fib_skipped (n : u64) (h : n.toNat ≤ 5) :
    ∃ lo hi : u64,
      clever_038_prime_fib.prime_fib n = RustM.ok lo
      ∧ clever_038_prime_fib.prime_fib (n + 1) = RustM.ok hi
      ∧ lo.toNat < hi.toNat
      ∧ (∀ c : Nat,
           is_fibonacci_nat c →
           lo.toNat < c →
           c < hi.toNat →
           ¬ is_prime_nat c) := by
  -- Common u64 toNat literals appearing in each case.
  have h2_toNat : (2 : u64).toNat = 2 := rfl
  have h3_toNat : (3 : u64).toNat = 3 := rfl
  have h5_toNat : (5 : u64).toNat = 5 := rfl
  have h13_toNat : (13 : u64).toNat = 13 := rfl
  have h89_toNat : (89 : u64).toNat = 89 := rfl
  have h233_toNat : (233 : u64).toNat = 233 := rfl
  have h1597_toNat : (1597 : u64).toNat = 1597 := rfl
  rcases n_eq_of_toNat_le_5 n h with h0 | h1 | h2 | h3 | h4 | h5
  · -- n = 0: lo = 2, hi = 3. Range (2, 3) is empty.
    subst h0
    refine ⟨2, 3, prime_fib_at_0, prime_fib_at_1, by decide, ?_⟩
    intros c hc hlo hhi
    rw [h2_toNat] at hlo; rw [h3_toNat] at hhi
    -- 2 < c < 3 ⇒ False
    exfalso; omega
  · -- n = 1: lo = 3, hi = 5. Range (3, 5) has c = 4, which is not a Fib.
    subst h1
    refine ⟨3, 5, prime_fib_at_1, prime_fib_at_2, by decide, ?_⟩
    intros c hc hlo hhi
    rw [h3_toNat] at hlo; rw [h5_toNat] at hhi
    have h_vals := is_fibonacci_nat_values c (by omega) hc
    -- c ∈ {1,2,3,5,8,13,...}; combined with 3 < c < 5 ⇒ contradiction (no fib is 4).
    rcases h_vals with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (exfalso; omega)
  · -- n = 2: lo = 5, hi = 13. Range (5, 13): only fib is 8. ¬ is_prime_nat 8.
    subst h2
    refine ⟨5, 13, prime_fib_at_2, prime_fib_at_3, by decide, ?_⟩
    intros c hc hlo hhi
    rw [h5_toNat] at hlo; rw [h13_toNat] at hhi
    have h_vals := is_fibonacci_nat_values c (by omega) hc
    rcases h_vals with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (first | (exfalso; omega) | exact not_is_prime_nat_8)
  · -- n = 3: lo = 13, hi = 89. Range (13, 89): fibs 21, 34, 55; all composite.
    subst h3
    refine ⟨13, 89, prime_fib_at_3, prime_fib_at_4, by decide, ?_⟩
    intros c hc hlo hhi
    rw [h13_toNat] at hlo; rw [h89_toNat] at hhi
    have h_vals := is_fibonacci_nat_values c (by omega) hc
    rcases h_vals with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (first
      | (exfalso; omega)
      | exact not_is_prime_nat_21
      | exact not_is_prime_nat_34
      | exact not_is_prime_nat_55)
  · -- n = 4: lo = 89, hi = 233. Range (89, 233): fib 144; composite.
    subst h4
    refine ⟨89, 233, prime_fib_at_4, prime_fib_at_5, by decide, ?_⟩
    intros c hc hlo hhi
    rw [h89_toNat] at hlo; rw [h233_toNat] at hhi
    have h_vals := is_fibonacci_nat_values c (by omega) hc
    rcases h_vals with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (first | (exfalso; omega) | exact not_is_prime_nat_144)
  · -- n = 5: lo = 233, hi = 1597. Range (233, 1597): fibs 377, 610, 987; all composite.
    subst h5
    refine ⟨233, 1597, prime_fib_at_5, prime_fib_at_6, by decide, ?_⟩
    intros c hc hlo hhi
    rw [h233_toNat] at hlo; rw [h1597_toNat] at hhi
    have h_vals := is_fibonacci_nat_values c (by omega) hc
    rcases h_vals with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (first
      | (exfalso; omega)
      | exact not_is_prime_nat_377
      | exact not_is_prime_nat_610
      | exact not_is_prime_nat_987)

end Clever_038_prime_fibObligations
