-- Companion obligations file for the `clever_145_get_max_triples` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_145_get_max_triples

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_145_get_max_triplesObligations

/-! ## Specification oracle (Nat-valued)

The Rust `naive_count` reference function transcribed at the `Nat` level.
We use 0-indexed array indices `i', j', k'` directly (matching the
`naive_count` test in the Rust source), where `ai_nat x = (x+1)^2 - (x+1) + 1`
mirrors `ai` on `Nat`.  Total on `Nat`. -/

/-- `ai_nat x = (x+1)^2 - (x+1) + 1` on `Nat`.  Equivalently `(x+1)*x + 1`. -/
private def ai_nat (x : Nat) : Nat :=
  let y := x + 1
  y * y - y + 1

/-- Inner sum: count of `k' ∈ [k_start, n)` such that
    `(ai_nat i + ai_nat j + ai_nat k') % 3 = 0`. -/
private def count_k_from (n i j : Nat) (k : Nat) : Nat :=
  if h : k < n then
    (if (ai_nat i + ai_nat j + ai_nat k) % 3 = 0 then 1 else 0)
      + count_k_from n i j (k + 1)
  else 0
termination_by n - k

/-- Middle sum: for fixed outer index `i`, count of `(j', k')` with
    `i < j' < k' < n` satisfying the mod-3 condition. -/
private def count_jk_from (n i : Nat) (j : Nat) : Nat :=
  if h : j < n then
    count_k_from n i j (j + 1) + count_jk_from n i (j + 1)
  else 0
termination_by n - j

/-- Outer sum: count of `(i', j', k')` with `i ≤ i' < j' < k' < n`. -/
private def count_ijk_from (n : Nat) (i : Nat) : Nat :=
  if h : i < n then
    count_jk_from n i (i + 1) + count_ijk_from n (i + 1)
  else 0
termination_by n - i

/-- Naive Nat-level count.  For `n < 3` there are no triples; otherwise
    count over `0 ≤ i' < j' < k' < n`. -/
private def naive_count_nat (n : Nat) : Nat :=
  if n < 3 then 0 else count_ijk_from n 0

/-! ## Contract clauses

The Rust source contains three contract-style tests in `mod tests`:
  * `known`         — three unit pins: `get_max_triples(5) = 1`,
                      `get_max_triples(0) = 0`, `get_max_triples(2) = 0`.
  * `below_three_is_zero` — boundary clause `n < 3 ⇒ result is 0`.
  * `matches_naive_count` — main postcondition: for every `n ∈ 0..=25`,
                            `get_max_triples(n)` equals `naive_count(n)`
                            (the independent imperative reference).

Each becomes one independent `theorem`.

### Feasibility note on `matches_naive_count`

The proptest exercises `n ∈ 0..=25`.  For very large `n` the universal
statement is *false* in the `u64` model:
  * `ai(n-1) = n^2 - n + 1` overflows for `n ≥ 2^32`;
  * the running sum `ai(i-1) + ai(j-1) + ai(k-1)` overflows when
    `3·ai(n-1) ≥ 2^64`, i.e. for `n ≳ 2^32/√3`;
  * the accumulator hits `2^64` when `C(n,3) ≥ 2^64`, i.e. for
    `n ≳ 4.8·10^6`.
The tightest constraint is the accumulator.  Rather than mimicking the
proptest's literal scope, we use a comfortable safe range
`n.toNat ≤ 25` that matches the proptest and trivially clears all three
overflow constraints. -/

/-! ## Helpers reused below. -/

private theorem u64_zero_toNat : ((0 : u64).toNat) = 0 := rfl
private theorem u64_one_toNat  : ((1 : u64).toNat) = 1 := rfl
private theorem u64_three_toNat : ((3 : u64).toNat) = 3 := rfl

/-! ## Boundary clause: `n < 3 ⇒ result is 0`.
Captures the proptest `below_three_is_zero`. -/
theorem get_max_triples_below_three_is_zero
    (n : u64) (h : n.toNat < 3) :
    clever_145_get_max_triples.get_max_triples n = RustM.ok (0 : u64) := by
  unfold clever_145_get_max_triples.get_max_triples
  have h_lt : n < (3 : u64) := by
    rw [UInt64.lt_iff_toNat_lt, u64_three_toNat]; exact h
  have h_dec : decide (n < (3 : u64)) = true := decide_eq_true h_lt
  simp only [show (n <? (3 : u64)) = (pure (decide (n < (3 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ## Main postcondition (functional correctness).
Captures the proptest `matches_naive_count`.

Strategy: since `n.toNat ≤ 25`, only 26 concrete values of `n` are
possible; on each, both sides reduce to closed `u64` literals via
`native_decide`.  We bridge `n` to `UInt64.ofNat n.toNat` then enumerate
the 26 cases. -/
theorem get_max_triples_matches_naive
    (n : u64) (h : n.toNat ≤ 25) :
    clever_145_get_max_triples.get_max_triples n
      = RustM.ok (UInt64.ofNat (naive_count_nat n.toNat)) := by
  -- Bridge n to UInt64.ofNat n.toNat to enable enumeration.
  have hn_inj : n = UInt64.ofNat n.toNat := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' n.toNat_lt]
  rw [hn_inj]
  -- Enumerate the 26 possible values of n.toNat.
  generalize hk : n.toNat = k at h
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
              k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨
              k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨
              k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 from by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals native_decide

/-! ## Unit pins from the `known` test. -/

/-- Unit pin: `get_max_triples 5 = 1`.  Verified by hand in the Rust
    source: array `[1, 3, 7, 13, 21]`, one triple `(1, 7, 13)` sums to
    `21`, divisible by 3. -/
theorem get_max_triples_at_5 :
    clever_145_get_max_triples.get_max_triples 5 = RustM.ok 1 := by
  native_decide

/-- Unit pin: `get_max_triples 0 = 0`.  Boundary `n < 3` short-circuits. -/
theorem get_max_triples_at_0 :
    clever_145_get_max_triples.get_max_triples 0 = RustM.ok 0 := by
  native_decide

/-- Unit pin: `get_max_triples 2 = 0`.  Boundary `n < 3` short-circuits. -/
theorem get_max_triples_at_2 :
    clever_145_get_max_triples.get_max_triples 2 = RustM.ok 0 := by
  native_decide

end Clever_145_get_max_triplesObligations
