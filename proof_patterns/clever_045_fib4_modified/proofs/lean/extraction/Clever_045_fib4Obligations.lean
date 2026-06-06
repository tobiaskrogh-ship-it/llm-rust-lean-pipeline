-- Companion obligations file for the `clever_045_fib4` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_045_fib4

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_045_fib4Obligations

/-! ## Base cases — unit pins

The Rust `base_cases` test asserts four specific seed values:
`fib4(0) = 0`, `fib4(1) = 0`, `fib4(2) = 2`, `fib4(3) = 0`. Each is one
independent contract clause; together they pin the seed of the 4-window
sliding recurrence and forbid trivial (all-zero or shifted) implementations
from satisfying the rest of the contract. `fib4_at` is defined via
`partial_fixpoint`, but the function is computable end-to-end, so each
unit pin is in principle dischargeable by `native_decide` evaluating the
fixpoint kernel by kernel (as in the `prime_fib` reference). -/

/-- `(0 : i64).toInt = 0`. Used to bridge the `n <? 0` comparison. -/
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-! ## Base cases via native_decide

`fib4_at` is extracted with `partial_fixpoint`, but the function is
computable end-to-end: `native_decide` evaluates the fixpoint kernel by
kernel, threading `RustM` through each iterative step. Mirrors the
`prime_fib_at_i` unit pins in the `clever_038_prime_fib` reference. -/

theorem fib4_at_zero :
    clever_045_fib4.fib4 (0 : i64) = RustM.ok (0 : i64) := by
  native_decide

theorem fib4_at_one :
    clever_045_fib4.fib4 (1 : i64) = RustM.ok (0 : i64) := by
  native_decide

theorem fib4_at_two :
    clever_045_fib4.fib4 (2 : i64) = RustM.ok (2 : i64) := by
  native_decide

theorem fib4_at_three :
    clever_045_fib4.fib4 (3 : i64) = RustM.ok (0 : i64) := by
  native_decide

/-! ## Negative-input sentinel

The `negative_inputs_return_zero` proptest asserts `fib4(n) = 0` for every
`n < 0`. This is the function's "out-of-domain" sentinel branch in the
public wrapper and is independent of any property of the tail-recursive
worker. -/

theorem fib4_negative_returns_zero (n : i64) (h : n.toInt < 0) :
    clever_045_fib4.fib4 n = RustM.ok (0 : i64) := by
  unfold clever_045_fib4.fib4
  have h_lt : decide (n < (0 : i64)) = true := by
    rw [decide_eq_true_iff, Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact h
  simp only [rust_primitives.cmp.lt, h_lt, pure_bind, ↓reduceIte]
  rfl

/-! ## Linear recurrence on the safe nonneg range

The `recurrence_on_nonneg_range` proptest asserts, for `n ∈ [4, 50]`, that
`fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4)`.  The bound
`n ≤ 50` keeps every intermediate value well below the i64 overflow
threshold (`fib4` grows ≈ 1.93^n; i64 fits up to roughly `n = 67`).

We package the recurrence as: in the safe range, all five calls succeed
and the integer-valued result satisfies the recurrence on `.toInt`. The
`.toInt` formulation matches the no-overflow regime: in the proptest's
range `[4, 50]`, the Rust wrapping i64 addition coincides with the
integer addition the test pretends to compute. -/

/-! ## Helpers for the linear recurrence

The recurrence is proved by enumerating `n` over the bounded range
`[4, 50]`.  For each concrete value, `native_decide` evaluates all five
`fib4` calls and the additive constraint by computation through the
`partial_fixpoint` kernel.  The conversion from `n.toInt ∈ [4, 50]` to
`n = (k : i64)` for a concrete `k` is via `Int64.ofInt_eq_of_toInt_eq`.
The witnesses are provided as `Int64.ofInt (fib4_oracle k)` — the
mathematical 4-step Fibonacci computed by Lean, avoiding manual literal
computation of f(44), ..., f(50). -/

/-- Tail-recursive accumulator for `fib4_oracle`: mirrors the Rust
    `fib4_at`'s 4-window slide, computing each value in O(n) steps. -/
private def fib4_oracle_aux : Nat → Int → Int → Int → Int → Int
  | 0,     a, _, _, _ => a
  | n + 1, a, b, c, d => fib4_oracle_aux n b c d (a + b + c + d)

/-- Mathematical 4-step Fibonacci: matches the `fib4_at` sliding window's
    interpretation on the safe nonneg range.  Implemented iteratively so
    `fib4_oracle k` evaluates in O(k) (the naive 4-way recursive form is
    O(4^k) and is impractical for `k ≥ 30`). -/
private def fib4_oracle (n : Nat) : Int :=
  fib4_oracle_aux n 0 0 2 0

/-- Overflow bound on `fib4_oracle` over `[0, 53]`: every value fits in i64.
    Used as scaffolding for the strong-induction reformulation of the
    recurrence (see `fib4_recurrence` docstring).  Proved by a single
    `native_decide` — fast because `fib4_oracle` is iterative (O(n)) and
    no `partial_fixpoint` evaluation is involved. -/
private theorem fib4_oracle_bounded :
    ∀ k : Nat, k ≤ 53 →
      -(2^63 : Int) ≤ fib4_oracle k ∧ fib4_oracle k < 2^63 := by
  native_decide

/-- Bundled equivalence: for every `k ∈ [0, 50]`, `fib4` on the i64 lift of
    `k` succeeds with value `Int64.ofInt (fib4_oracle k)`.  Proved by a
    single `native_decide` so all 51 cases share one native compile/link
    cycle.  With the iterative `fib4_oracle` (O(n) eval), the cumulative
    cost is ≤ O(50²) Nat/Int ops + 51 partial_fixpoint evaluations of
    length ≤ 50, which fits the build budget. -/
private theorem fib4_eq_oracle :
    ∀ k : Nat, k ≤ 50 →
      clever_045_fib4.fib4 (Int64.ofNat k) =
        RustM.ok (Int64.ofInt (fib4_oracle k)) := by
  native_decide

/-- Mathematical recurrence at the oracle level, over `[0, 50]`:
    `fib4_oracle (k+4) = fib4_oracle (k+3) + fib4_oracle (k+2) +
                         fib4_oracle (k+1) + fib4_oracle k`.
    Proved by a single `native_decide`; the iterative `fib4_oracle`
    makes this a pure `Nat`-recursive check with no `partial_fixpoint`
    involvement. -/
private theorem fib4_oracle_rec :
    ∀ k : Nat, k ≤ 50 →
      fib4_oracle (k + 4) =
        fib4_oracle (k + 3) + fib4_oracle (k + 2) +
        fib4_oracle (k + 1) + fib4_oracle k := by
  native_decide

/-- i64 subtraction by a small `Nat` literal commutes with `Int64.ofNat`
    on the safe range.  For `m ∈ [0, 46]`, with `k := m + 4 ∈ [4, 50]`,
    `Int64.ofNat k - Int64.ofNat j = Int64.ofNat (k - j)` for each
    `j ∈ {1,2,3,4}` since no underflow occurs and the result fits in
    i64.  Phrased with the single bound `m < 47` so Lean's
    `Nat.decBallLT` synthesises the `Decidable` instance for the
    bounded universal automatically. -/
private theorem int64_ofNat_sub :
    ∀ m : Nat, m < 47 →
      (Int64.ofNat (m + 4) - 1 : i64) = Int64.ofNat (m + 4 - 1) ∧
      (Int64.ofNat (m + 4) - 2 : i64) = Int64.ofNat (m + 4 - 2) ∧
      (Int64.ofNat (m + 4) - 3 : i64) = Int64.ofNat (m + 4 - 3) ∧
      (Int64.ofNat (m + 4) - 4 : i64) = Int64.ofNat (m + 4 - 4) := by
  native_decide

/-- The `.toInt` round-trip on `Int64.ofInt (fib4_oracle k)` for
    `k ∈ [0, 53]`: extracts the underlying `Int` back unchanged because
    the value fits in i64. -/
private theorem fib4_oracle_toInt_ofInt
    (k : Nat) (h : k ≤ 53) :
    (Int64.ofInt (fib4_oracle k) : i64).toInt = fib4_oracle k := by
  have ⟨hlo, hhi⟩ := fib4_oracle_bounded k h
  exact Int64.toInt_ofInt_of_le hlo hhi

/-
-- A previous attempt at the recurrence enumerated `n` as one of 47
-- concrete values in `[4, 50]` via an `omega`-driven 47-way
-- disjunction, then closed each case with `native_decide` over
-- `fib4_oracle`.  That approach is sound but exceeds the build
-- timeout (47 separate `native_decide` invocations × ~5 s each).
-- The current proof goes through `int64_ofNat_sub` and
-- `fib4_eq_oracle` instead, sharing a single `native_decide`
-- compilation across all bounded universals.
-/

-- The dead 47-arm enumeration helper has been removed; the recurrence
-- proof below uses the bridging lemmas (`int64_ofNat_sub`,
-- `fib4_eq_oracle`, `fib4_oracle_rec`, `fib4_oracle_toInt_ofInt`)
-- instead.

/-- Linear recurrence on the safe nonneg range `[4, 50]`:
    `fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4)` (under
    `.toInt`).

    The proof projects `n` to a `Nat` index `k := n.toInt.toNat ∈
    [4, 50]`, shifts to `m := k - 4 ∈ [0, 46]` so `int64_ofNat_sub`
    applies, derives `n = Int64.ofNat k` from
    `Int64.ofInt_eq_of_toInt_eq`, converts each `n - j` into
    `Int64.ofNat (k - j)` for `j ∈ {1,2,3,4}` via `int64_ofNat_sub`,
    applies `fib4_eq_oracle` at `k, k-1, k-2, k-3, k-4` to pull the
    five `fib4 (Int64.ofNat _)` values back to
    `Int64.ofInt (fib4_oracle _)`, then closes the `.toInt` additive
    identity via `fib4_oracle_toInt_ofInt` (each round-trip preserves
    the value because `fib4_oracle_bounded` shows it fits in i64) and
    `fib4_oracle_rec` (the mathematical recurrence at the oracle
    level).  All four bridging lemmas are proved by a single
    `native_decide` over a single bounded universal (`∀ k ≤ N, …`),
    so the cumulative native compilation cost is small. -/
theorem fib4_recurrence
    (n : i64) (h_lo : 4 ≤ n.toInt) (h_hi : n.toInt ≤ 50) :
    ∃ v vm1 vm2 vm3 vm4 : i64,
      clever_045_fib4.fib4 n       = RustM.ok v ∧
      clever_045_fib4.fib4 (n - 1) = RustM.ok vm1 ∧
      clever_045_fib4.fib4 (n - 2) = RustM.ok vm2 ∧
      clever_045_fib4.fib4 (n - 3) = RustM.ok vm3 ∧
      clever_045_fib4.fib4 (n - 4) = RustM.ok vm4 ∧
      v.toInt = vm1.toInt + vm2.toInt + vm3.toInt + vm4.toInt := by
  -- Step 1: Project n to a `Nat` index `k = n.toInt.toNat` with k ∈ [4, 50].
  let k : Nat := n.toInt.toNat
  let m : Nat := k - 4
  have h_k_ge_4 : 4 ≤ k := by show 4 ≤ n.toInt.toNat; omega
  have h_k_le_50 : k ≤ 50 := by show n.toInt.toNat ≤ 50; omega
  -- Step 2: Shift to `m = k - 4` so the `int64_ofNat_sub` lemma applies.
  have h_m_lt : m < 47 := by show k - 4 < 47; omega
  have h_k_eq_m : k = m + 4 := by show k = (k - 4) + 4; omega
  -- Step 3: n = Int64.ofNat k.
  have h_n_eq : n = Int64.ofNat k := by
    have h_int_eq : (k : Int) = n.toInt := by
      show (n.toInt.toNat : Int) = n.toInt; omega
    have h_ofInt : Int64.ofInt n.toInt = n := Int64.ofInt_eq_of_toInt_eq rfl
    show n = Int64.ofInt (k : Int)
    rw [h_int_eq]; exact h_ofInt.symm
  -- Step 4: n - j = Int64.ofNat (k - j) for j ∈ {1, 2, 3, 4}.
  obtain ⟨h_sub1, h_sub2, h_sub3, h_sub4⟩ := int64_ofNat_sub m h_m_lt
  have h_km1 : k - 1 = m + 4 - 1 := by rw [h_k_eq_m]
  have h_km2 : k - 2 = m + 4 - 2 := by rw [h_k_eq_m]
  have h_km3 : k - 3 = m + 4 - 3 := by rw [h_k_eq_m]
  have h_km4 : k - 4 = m + 4 - 4 := by rw [h_k_eq_m]
  -- Step 5: Apply `fib4_eq_oracle` at k, k-1, ..., k-4.
  have h_fib_k  : clever_045_fib4.fib4 (Int64.ofNat k) =
                    RustM.ok (Int64.ofInt (fib4_oracle k)) :=
    fib4_eq_oracle k h_k_le_50
  have h_fib_m1 : clever_045_fib4.fib4 (Int64.ofNat (k - 1)) =
                    RustM.ok (Int64.ofInt (fib4_oracle (k - 1))) :=
    fib4_eq_oracle (k - 1) (by omega)
  have h_fib_m2 : clever_045_fib4.fib4 (Int64.ofNat (k - 2)) =
                    RustM.ok (Int64.ofInt (fib4_oracle (k - 2))) :=
    fib4_eq_oracle (k - 2) (by omega)
  have h_fib_m3 : clever_045_fib4.fib4 (Int64.ofNat (k - 3)) =
                    RustM.ok (Int64.ofInt (fib4_oracle (k - 3))) :=
    fib4_eq_oracle (k - 3) (by omega)
  have h_fib_m4 : clever_045_fib4.fib4 (Int64.ofNat (k - 4)) =
                    RustM.ok (Int64.ofInt (fib4_oracle (k - 4))) :=
    fib4_eq_oracle (k - 4) (by omega)
  -- Step 6: toInt round-trips for each witness (all values fit in i64).
  have h_t_k  := fib4_oracle_toInt_ofInt k       (by omega)
  have h_t_m1 := fib4_oracle_toInt_ofInt (k - 1) (by omega)
  have h_t_m2 := fib4_oracle_toInt_ofInt (k - 2) (by omega)
  have h_t_m3 := fib4_oracle_toInt_ofInt (k - 3) (by omega)
  have h_t_m4 := fib4_oracle_toInt_ofInt (k - 4) (by omega)
  -- Step 7: Oracle-level recurrence at index k.
  have h_rec : fib4_oracle k =
      fib4_oracle (k - 1) + fib4_oracle (k - 2) +
      fib4_oracle (k - 3) + fib4_oracle (k - 4) := by
    rw [h_k_eq_m]
    show fib4_oracle (m + 4) =
         fib4_oracle (m + 4 - 1) + fib4_oracle (m + 4 - 2) +
         fib4_oracle (m + 4 - 3) + fib4_oracle (m + 4 - 4)
    show fib4_oracle (m + 4) =
         fib4_oracle (m + 3) + fib4_oracle (m + 2) +
         fib4_oracle (m + 1) + fib4_oracle m
    exact fib4_oracle_rec m (by omega)
  -- Step 8: Take witnesses and discharge each conjunct.
  refine ⟨Int64.ofInt (fib4_oracle k),
          Int64.ofInt (fib4_oracle (k - 1)),
          Int64.ofInt (fib4_oracle (k - 2)),
          Int64.ofInt (fib4_oracle (k - 3)),
          Int64.ofInt (fib4_oracle (k - 4)),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_n_eq]; exact h_fib_k
  · rw [h_n_eq, h_k_eq_m, h_sub1, ← h_km1]; exact h_fib_m1
  · rw [h_n_eq, h_k_eq_m, h_sub2, ← h_km2]; exact h_fib_m2
  · rw [h_n_eq, h_k_eq_m, h_sub3, ← h_km3]; exact h_fib_m3
  · rw [h_n_eq, h_k_eq_m, h_sub4, ← h_km4]; exact h_fib_m4
  · rw [h_t_k, h_t_m1, h_t_m2, h_t_m3, h_t_m4]; exact h_rec

end Clever_045_fib4Obligations
