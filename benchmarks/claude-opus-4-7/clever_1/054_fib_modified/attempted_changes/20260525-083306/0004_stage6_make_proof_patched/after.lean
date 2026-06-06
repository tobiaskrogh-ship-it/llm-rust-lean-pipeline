-- Companion obligations file for the `clever_048_fib` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_048_fib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_048_fibObligations

/-! ## Base cases — unit pins (from the Rust `base_cases` test)

The test asserts six specific seed values:
`fib(0) = 0`, `fib(1) = 1`, `fib(2) = 1`, `fib(3) = 2`, `fib(4) = 3`,
`fib(5) = 5`. Each is one independent contract clause; together they pin
the seed of the 2-window sliding recurrence and forbid trivial (all-zero
or shifted) implementations from satisfying the rest of the contract.
`fib_at` is defined via `partial_fixpoint`, but the function is computable
end-to-end, so each unit pin is in principle dischargeable by
`native_decide` evaluating the fixpoint kernel by kernel (mirrors the
`fib4_at_*` and `prime_fib_at_*` unit pins in the references). -/

theorem fib_zero :
    clever_048_fib.fib (0 : i64) = RustM.ok (0 : i64) := by
  native_decide

theorem fib_one :
    clever_048_fib.fib (1 : i64) = RustM.ok (1 : i64) := by
  native_decide

theorem fib_two :
    clever_048_fib.fib (2 : i64) = RustM.ok (1 : i64) := by
  native_decide

theorem fib_three :
    clever_048_fib.fib (3 : i64) = RustM.ok (2 : i64) := by
  native_decide

theorem fib_four :
    clever_048_fib.fib (4 : i64) = RustM.ok (3 : i64) := by
  native_decide

theorem fib_five :
    clever_048_fib.fib (5 : i64) = RustM.ok (5 : i64) := by
  native_decide

/-! ## Negative-input sentinel (from `negative_collapses_to_zero`)

The proptest asserts `fib(n) = 0` for every `n ∈ [-5, 0)`. The natural
Lean generalisation: for every `n < 0` the function returns `Ok 0`. This
is the function's "out-of-domain" sentinel branch in the public wrapper
and is independent of any property of the tail-recursive worker. -/

/-- `(0 : i64).toInt = 0`. Used to bridge the `n <? 0` comparison. -/
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

theorem fib_negative_returns_zero (n : i64) (h : n.toInt < 0) :
    clever_048_fib.fib n = RustM.ok (0 : i64) := by
  unfold clever_048_fib.fib
  have h_lt : decide (n < (0 : i64)) = true := by
    rw [decide_eq_true_iff, Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact h
  simp only [rust_primitives.cmp.lt, h_lt, pure_bind, ↓reduceIte]
  rfl

/-! ## Linear recurrence on the safe nonneg range
       (from `recurrence_on_nonneg_range`)

The proptest asserts, for `n ∈ [2, 80]`, that
`fib(n) = fib(n-1) + fib(n-2)`. The proptest's `n ≤ 80` is conservative;
the true truth-domain in the Lean model is `n ≤ 91`, since `fib_at`
accumulates `b = fib(k+1)` and computes `a + b = fib(k+2)` as an
intermediate before exiting at `k = n`, so the binding constraint is
`fib(n+1) < 2^63`.  Concretely `fib(92) ≈ 7.54·10^18 < 2^63 ≈ 9.22·10^18`
fits, while `fib(93) ≈ 1.22·10^19` overflows. Hence `fib n` succeeds for
`n.toInt ∈ [0, 91]`, and the recurrence stays inside the no-overflow
regime for `n.toInt ∈ [2, 91]`.

We package the recurrence as: in the safe range, all three calls succeed
and the integer-valued results satisfy the recurrence on `.toInt`. The
`.toInt` formulation matches the no-overflow regime: in `[2, 91]`, the
Rust wrapping i64 addition coincides with the integer addition the test
pretends to compute. -/

/-! ## Helpers for the linear recurrence

The recurrence is proved by enumerating `n` over the bounded range
`[2, 91]`. The conversion from `n.toInt ∈ [2, 91]` to `n = (k : i64)`
for a concrete `k` is via `Int64.ofInt_eq_of_toInt_eq`. The witnesses are
provided as `Int64.ofInt (fib_oracle k)` — the mathematical Fibonacci
computed by Lean, avoiding manual literal computation of f(89), f(90),
f(91). Mirrors the fib4 reference's structure with 2 witnesses instead
of 4. -/

/-- Tail-recursive accumulator for `fib_oracle`: mirrors the Rust
    `fib_at`'s 2-window slide, computing each value in O(n) steps. -/
private def fib_oracle_aux : Nat → Int → Int → Int
  | 0,     a, _ => a
  | n + 1, a, b => fib_oracle_aux n b (a + b)

/-- Mathematical Fibonacci: matches the `fib_at` sliding window's
    interpretation on the safe nonneg range. Implemented iteratively so
    `fib_oracle k` evaluates in O(k). -/
private def fib_oracle (n : Nat) : Int :=
  fib_oracle_aux n 0 1

/-- Overflow bound on `fib_oracle` over `[0, 91]`: every value fits in i64.
    Proved by a single `native_decide` — fast because `fib_oracle` is
    iterative (O(n)) and no `partial_fixpoint` evaluation is involved. -/
private theorem fib_oracle_bounded :
    ∀ k : Nat, k ≤ 91 →
      -(2^63 : Int) ≤ fib_oracle k ∧ fib_oracle k < 2^63 := by
  native_decide

/-- Bundled equivalence: for every `k ∈ [0, 91]`, `fib` on the i64 lift of
    `k` succeeds with value `Int64.ofInt (fib_oracle k)`. Proved by a
    single `native_decide` so all 92 cases share one native compile/link
    cycle. -/
private theorem fib_eq_oracle :
    ∀ k : Nat, k ≤ 91 →
      clever_048_fib.fib (Int64.ofNat k) =
        RustM.ok (Int64.ofInt (fib_oracle k)) := by
  native_decide

/-- Mathematical recurrence at the oracle level, over `[0, 89]`:
    `fib_oracle (k + 2) = fib_oracle (k + 1) + fib_oracle k`.
    Proved by a single `native_decide`; the iterative `fib_oracle`
    makes this a pure `Nat`-recursive check with no `partial_fixpoint`
    involvement. -/
private theorem fib_oracle_rec :
    ∀ k : Nat, k ≤ 89 →
      fib_oracle (k + 2) = fib_oracle (k + 1) + fib_oracle k := by
  native_decide

/-- i64 subtraction by a small `Nat` literal commutes with `Int64.ofNat`
    on the safe range. For `m ∈ [0, 89]`, with `k := m + 2 ∈ [2, 91]`,
    `Int64.ofNat k - Int64.ofNat j = Int64.ofNat (k - j)` for each
    `j ∈ {1, 2}` since no underflow occurs and the result fits in i64. -/
private theorem int64_ofNat_sub :
    ∀ m : Nat, m < 90 →
      (Int64.ofNat (m + 2) - 1 : i64) = Int64.ofNat (m + 2 - 1) ∧
      (Int64.ofNat (m + 2) - 2 : i64) = Int64.ofNat (m + 2 - 2) := by
  native_decide

/-- The `.toInt` round-trip on `Int64.ofInt (fib_oracle k)` for
    `k ∈ [0, 91]`: extracts the underlying `Int` back unchanged because
    the value fits in i64. -/
private theorem fib_oracle_toInt_ofInt
    (k : Nat) (h : k ≤ 91) :
    (Int64.ofInt (fib_oracle k) : i64).toInt = fib_oracle k := by
  have ⟨hlo, hhi⟩ := fib_oracle_bounded k h
  exact Int64.toInt_ofInt_of_le hlo hhi

/-- Linear recurrence on the safe nonneg range `[2, 91]`:
    `fib(n) = fib(n-1) + fib(n-2)` (under `.toInt`).

    The proof projects `n` to a `Nat` index `k := n.toInt.toNat ∈
    [2, 91]`, shifts to `m := k - 2 ∈ [0, 89]` so `int64_ofNat_sub`
    applies, derives `n = Int64.ofNat k` from
    `Int64.ofInt_eq_of_toInt_eq`, converts each `n - j` into
    `Int64.ofNat (k - j)` for `j ∈ {1, 2}` via `int64_ofNat_sub`,
    applies `fib_eq_oracle` at `k, k-1, k-2` to pull the three
    `fib (Int64.ofNat _)` values back to `Int64.ofInt (fib_oracle _)`,
    then closes the `.toInt` additive identity via
    `fib_oracle_toInt_ofInt` and `fib_oracle_rec`. -/
theorem fib_recurrence
    (n : i64) (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt ≤ 91) :
    ∃ v vm1 vm2 : i64,
      clever_048_fib.fib n       = RustM.ok v ∧
      clever_048_fib.fib (n - 1) = RustM.ok vm1 ∧
      clever_048_fib.fib (n - 2) = RustM.ok vm2 ∧
      v.toInt = vm1.toInt + vm2.toInt := by
  -- Step 1: Project n to a `Nat` index `k = n.toInt.toNat` with k ∈ [2, 91].
  let k : Nat := n.toInt.toNat
  let m : Nat := k - 2
  have h_k_ge_2 : 2 ≤ k := by show 2 ≤ n.toInt.toNat; omega
  have h_k_le_91 : k ≤ 91 := by show n.toInt.toNat ≤ 91; omega
  -- Step 2: Shift to `m = k - 2` so the `int64_ofNat_sub` lemma applies.
  have h_m_lt : m < 90 := by show k - 2 < 90; omega
  have h_k_eq_m : k = m + 2 := by show k = (k - 2) + 2; omega
  -- Step 3: n = Int64.ofNat k.
  have h_n_eq : n = Int64.ofNat k := by
    have h_int_eq : (k : Int) = n.toInt := by
      show (n.toInt.toNat : Int) = n.toInt; omega
    have h_ofInt : Int64.ofInt n.toInt = n := Int64.ofInt_eq_of_toInt_eq rfl
    show n = Int64.ofInt (k : Int)
    rw [h_int_eq]; exact h_ofInt.symm
  -- Step 4: n - j = Int64.ofNat (k - j) for j ∈ {1, 2}.
  obtain ⟨h_sub1, h_sub2⟩ := int64_ofNat_sub m h_m_lt
  have h_km1 : k - 1 = m + 2 - 1 := by rw [h_k_eq_m]
  have h_km2 : k - 2 = m + 2 - 2 := by rw [h_k_eq_m]
  -- Step 5: Apply `fib_eq_oracle` at k, k-1, k-2.
  have h_fib_k  : clever_048_fib.fib (Int64.ofNat k) =
                    RustM.ok (Int64.ofInt (fib_oracle k)) :=
    fib_eq_oracle k h_k_le_91
  have h_fib_m1 : clever_048_fib.fib (Int64.ofNat (k - 1)) =
                    RustM.ok (Int64.ofInt (fib_oracle (k - 1))) :=
    fib_eq_oracle (k - 1) (by omega)
  have h_fib_m2 : clever_048_fib.fib (Int64.ofNat (k - 2)) =
                    RustM.ok (Int64.ofInt (fib_oracle (k - 2))) :=
    fib_eq_oracle (k - 2) (by omega)
  -- Step 6: toInt round-trips for each witness (all values fit in i64).
  have h_t_k  := fib_oracle_toInt_ofInt k       (by omega)
  have h_t_m1 := fib_oracle_toInt_ofInt (k - 1) (by omega)
  have h_t_m2 := fib_oracle_toInt_ofInt (k - 2) (by omega)
  -- Step 7: Oracle-level recurrence at index k.
  have h_rec : fib_oracle k =
      fib_oracle (k - 1) + fib_oracle (k - 2) := by
    rw [h_k_eq_m]
    show fib_oracle (m + 2) =
         fib_oracle (m + 2 - 1) + fib_oracle (m + 2 - 2)
    show fib_oracle (m + 2) =
         fib_oracle (m + 1) + fib_oracle m
    exact fib_oracle_rec m (by omega)
  -- Step 8: Take witnesses and discharge each conjunct.
  refine ⟨Int64.ofInt (fib_oracle k),
          Int64.ofInt (fib_oracle (k - 1)),
          Int64.ofInt (fib_oracle (k - 2)),
          ?_, ?_, ?_, ?_⟩
  · rw [h_n_eq]; exact h_fib_k
  · rw [h_n_eq, h_k_eq_m, h_sub1, ← h_km1]; exact h_fib_m1
  · rw [h_n_eq, h_k_eq_m, h_sub2, ← h_km2]; exact h_fib_m2
  · rw [h_t_k, h_t_m1, h_t_m2]; exact h_rec

end Clever_048_fibObligations
