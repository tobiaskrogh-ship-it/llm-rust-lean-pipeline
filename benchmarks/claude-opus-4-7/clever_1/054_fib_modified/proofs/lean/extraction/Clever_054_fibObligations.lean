-- Companion obligations file for the `clever_054_fib` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_054_fib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_054_fibObligations

/-! ## Base cases — unit pins

The Rust `base_cases` test asserts six specific seed values:
`fib(0) = 0`, `fib(1) = 1`, `fib(2) = 1`, `fib(3) = 2`, `fib(4) = 3`, `fib(5) = 5`.
Each is an independent contract clause; together they pin the seed of the
2-window sliding recurrence and forbid trivial (all-zero) implementations
from satisfying the rest of the contract. `fib_at` is defined via
`partial_fixpoint`, but the function is computable end-to-end so each
unit pin is in principle dischargeable by `native_decide` evaluating the
fixpoint kernel by kernel (as in the `clever_045_fib4` and
`clever_038_prime_fib` references). -/

theorem fib_at_0 :
    clever_054_fib.fib (0 : u64) = RustM.ok (0 : u64) := by
  native_decide

theorem fib_at_1 :
    clever_054_fib.fib (1 : u64) = RustM.ok (1 : u64) := by
  native_decide

theorem fib_at_2 :
    clever_054_fib.fib (2 : u64) = RustM.ok (1 : u64) := by
  native_decide

theorem fib_at_3 :
    clever_054_fib.fib (3 : u64) = RustM.ok (2 : u64) := by
  native_decide

theorem fib_at_4 :
    clever_054_fib.fib (4 : u64) = RustM.ok (3 : u64) := by
  native_decide

theorem fib_at_5 :
    clever_054_fib.fib (5 : u64) = RustM.ok (5 : u64) := by
  native_decide

/-! ## Linear recurrence on the safe range

The `recurrence` proptest asserts, for `n ∈ [2, 80]`, that
`fib(n) = fib(n - 1) + fib(n - 2)`.

### Feasibility analysis

`fib_at(n, 0, 1, 0)` iterates `k = 0, ..., n - 1`, maintaining the
invariant `(a, b) = (fib k, fib (k+1))`.  The last step at `k = n - 1`
computes `a + b = fib(n+1)`, then the base case returns `a = fib(n)`.
Hence `fib(n)` succeeds in the Lean model iff `fib(n+1) < 2^64`.

  - `fib(93) = 12_200_160_415_121_876_738 < 2^64`
  - `fib(94) = 19_740_274_219_868_223_167 > 2^64`

So `fib(n)` succeeds for `n.toNat ≤ 92` and fails (integer overflow)
for `n.toNat ≥ 93`.  The strongest honest universal recurrence is
therefore `n.toNat ∈ [2, 92]`, well beyond the proptest's
conservative `[2, 80]` range.  Within that range all three calls
succeed and the u64 addition does not wrap, so the postcondition
can be stated at the `.toNat` level. -/

/-! ## Helpers for the linear recurrence

The recurrence is proved by enumerating `n` over the bounded range
`[2, 92]`.  For each concrete value, `native_decide` evaluates all three
`fib` calls and the additive constraint by computation through the
`partial_fixpoint` kernel.  The conversion from `n.toNat ∈ [2, 92]` to
`n = (k : u64)` for a concrete `k` is via `UInt64.ofNat_eq_of_toNat_eq`.
The witnesses are provided as `UInt64.ofNat (fib_oracle k)` — the
mathematical Fibonacci computed by Lean, avoiding manual literal
computation of f(80), ..., f(92). -/

/-- Tail-recursive accumulator for `fib_oracle`: mirrors the Rust
    `fib_at`'s 2-window slide, computing each value in O(n) steps. -/
private def fib_oracle_aux : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fib_oracle_aux n b (a + b)

/-- Mathematical Fibonacci: matches the `fib_at` sliding window's
    interpretation on the safe range.  Implemented iteratively so
    `fib_oracle k` evaluates in O(k) (the naive 2-way recursive form
    is O(2^k) and impractical for `k ≥ 30`). -/
private def fib_oracle (n : Nat) : Nat :=
  fib_oracle_aux n 0 1

/-- Overflow bound on `fib_oracle` over `[0, 93]`: every value fits in u64.
    Used as scaffolding for the recurrence (see `fib_recurrence` docstring).
    Proved by a single `native_decide` — fast because `fib_oracle` is
    iterative (O(n)) and no `partial_fixpoint` evaluation is involved.
    The bound is `93` because the recurrence proof at `n = 92` requires
    `fib_oracle (k+1)` to fit (and `fib(93) < 2^64 < fib(94)`). -/
private theorem fib_oracle_bounded :
    ∀ k : Nat, k ≤ 93 → fib_oracle k < 2 ^ 64 := by
  native_decide

/-- Bundled equivalence: for every `k ∈ [0, 92]`, `fib` on the u64 lift
    of `k` succeeds with value `UInt64.ofNat (fib_oracle k)`.  Proved by
    a single `native_decide` so all 93 cases share one native compile/link
    cycle. -/
private theorem fib_eq_oracle :
    ∀ k : Nat, k ≤ 92 →
      clever_054_fib.fib (UInt64.ofNat k) =
        RustM.ok (UInt64.ofNat (fib_oracle k)) := by
  native_decide

/-- Mathematical recurrence at the oracle level, over `[0, 92]`:
    `fib_oracle (k+2) = fib_oracle (k+1) + fib_oracle k`.
    Proved by a single `native_decide`; the iterative `fib_oracle`
    makes this a pure `Nat`-recursive check with no `partial_fixpoint`
    involvement. -/
private theorem fib_oracle_rec :
    ∀ k : Nat, k ≤ 92 →
      fib_oracle (k + 2) = fib_oracle (k + 1) + fib_oracle k := by
  native_decide

/-- u64 subtraction by a small `Nat` literal commutes with `UInt64.ofNat`
    on the safe range.  For `m ∈ [0, 90]`, with `k := m + 2 ∈ [2, 92]`,
    `UInt64.ofNat k - UInt64.ofNat j = UInt64.ofNat (k - j)` for each
    `j ∈ {1, 2}` since no underflow occurs and the result fits in u64. -/
private theorem u64_ofNat_sub :
    ∀ m : Nat, m < 91 →
      (UInt64.ofNat (m + 2) - 1 : u64) = UInt64.ofNat (m + 2 - 1) ∧
      (UInt64.ofNat (m + 2) - 2 : u64) = UInt64.ofNat (m + 2 - 2) := by
  native_decide

/-- The `.toNat` round-trip on `UInt64.ofNat (fib_oracle k)` for
    `k ∈ [0, 93]`: extracts the underlying `Nat` back unchanged because
    the value fits in u64. -/
private theorem fib_oracle_toNat_ofNat
    (k : Nat) (h : k ≤ 93) :
    (UInt64.ofNat (fib_oracle k) : u64).toNat = fib_oracle k :=
  UInt64.toNat_ofNat_of_lt' (fib_oracle_bounded k h)

/-- Linear recurrence on the safe range `[2, 92]`:
    `fib(n) = fib(n-1) + fib(n-2)` (under `.toNat`, no wrap-around).

    The proof projects `n` to a `Nat` index `k := n.toNat ∈ [2, 92]`,
    shifts to `m := k - 2 ∈ [0, 90]` so `u64_ofNat_sub` applies, derives
    `n = UInt64.ofNat k` from `UInt64.ofNat_eq_of_toNat_eq`, converts
    `n - 1` and `n - 2` into `UInt64.ofNat (k - 1)` / `UInt64.ofNat (k - 2)`
    via `u64_ofNat_sub`, applies `fib_eq_oracle` at `k, k-1, k-2` to pull
    the three `fib (UInt64.ofNat _)` values back to
    `UInt64.ofNat (fib_oracle _)`, then closes the `.toNat` additive
    identity via `fib_oracle_toNat_ofNat` and `fib_oracle_rec`. -/
theorem fib_recurrence
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat ≤ 92) :
    ∃ v vm1 vm2 : u64,
      clever_054_fib.fib n       = RustM.ok v ∧
      clever_054_fib.fib (n - 1) = RustM.ok vm1 ∧
      clever_054_fib.fib (n - 2) = RustM.ok vm2 ∧
      v.toNat = vm1.toNat + vm2.toNat := by
  -- Step 1: Project n to a `Nat` index `k = n.toNat` with k ∈ [2, 92].
  let k : Nat := n.toNat
  let m : Nat := k - 2
  have h_k_ge_2 : 2 ≤ k := h_lo
  have h_k_le_92 : k ≤ 92 := h_hi
  -- Step 2: Shift to `m = k - 2` so the `u64_ofNat_sub` lemma applies.
  have h_m_lt : m < 91 := by show k - 2 < 91; omega
  have h_k_eq_m : k = m + 2 := by show k = (k - 2) + 2; omega
  -- Step 3: n = UInt64.ofNat k.
  have h_n_eq : n = UInt64.ofNat k :=
    (UInt64.ofNat_eq_of_toNat_eq rfl).symm
  -- Step 4: n - j = UInt64.ofNat (k - j) for j ∈ {1, 2}.
  obtain ⟨h_sub1, h_sub2⟩ := u64_ofNat_sub m h_m_lt
  have h_km1 : k - 1 = m + 2 - 1 := by rw [h_k_eq_m]
  have h_km2 : k - 2 = m + 2 - 2 := by rw [h_k_eq_m]
  -- Step 5: Apply `fib_eq_oracle` at k, k-1, k-2.
  have h_fib_k  : clever_054_fib.fib (UInt64.ofNat k) =
                    RustM.ok (UInt64.ofNat (fib_oracle k)) :=
    fib_eq_oracle k h_k_le_92
  have h_fib_m1 : clever_054_fib.fib (UInt64.ofNat (k - 1)) =
                    RustM.ok (UInt64.ofNat (fib_oracle (k - 1))) :=
    fib_eq_oracle (k - 1) (by omega)
  have h_fib_m2 : clever_054_fib.fib (UInt64.ofNat (k - 2)) =
                    RustM.ok (UInt64.ofNat (fib_oracle (k - 2))) :=
    fib_eq_oracle (k - 2) (by omega)
  -- Step 6: toNat round-trips for each witness (all values fit in u64).
  have h_t_k  := fib_oracle_toNat_ofNat k       (by omega)
  have h_t_m1 := fib_oracle_toNat_ofNat (k - 1) (by omega)
  have h_t_m2 := fib_oracle_toNat_ofNat (k - 2) (by omega)
  -- Step 7: Oracle-level recurrence at index k.
  have h_rec : fib_oracle k = fib_oracle (k - 1) + fib_oracle (k - 2) := by
    rw [h_k_eq_m]
    show fib_oracle (m + 2) = fib_oracle (m + 2 - 1) + fib_oracle (m + 2 - 2)
    show fib_oracle (m + 2) = fib_oracle (m + 1) + fib_oracle m
    exact fib_oracle_rec m (by omega)
  -- Step 8: Take witnesses and discharge each conjunct.
  refine ⟨UInt64.ofNat (fib_oracle k),
          UInt64.ofNat (fib_oracle (k - 1)),
          UInt64.ofNat (fib_oracle (k - 2)),
          ?_, ?_, ?_, ?_⟩
  · rw [h_n_eq]; exact h_fib_k
  · rw [h_n_eq, h_k_eq_m, h_sub1, ← h_km1]; exact h_fib_m1
  · rw [h_n_eq, h_k_eq_m, h_sub2, ← h_km2]; exact h_fib_m2
  · rw [h_t_k, h_t_m1, h_t_m2]; exact h_rec

end Clever_054_fibObligations
