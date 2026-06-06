-- Companion obligations file for the `clever_049_fibfib` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_049_fibfib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_049_fibfibObligations

/-! ## Base cases — unit pins (from the `base_cases` Rust test)

The Rust `base_cases` test asserts seven specific seed values:
`fibfib(0) = 0`, `fibfib(1) = 0`, `fibfib(2) = 1`, `fibfib(3) = 1`,
`fibfib(4) = 2`, `fibfib(5) = 4`, `fibfib(6) = 7`. Each is one
independent contract clause; together they pin the seed of the 3-window
sliding recurrence and forbid trivial (all-zero or shifted)
implementations from satisfying the rest of the contract. `fibfib_at`
is defined via `partial_fixpoint`, but the function is computable
end-to-end, so each unit pin is dischargeable by `native_decide`
evaluating the fixpoint kernel by kernel. -/

/-- `(0 : i64).toInt = 0`. Used to bridge the `n <? 0` comparison
    in `fibfib_negative_returns_zero`. -/
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

theorem fibfib_at_zero :
    clever_049_fibfib.fibfib (0 : i64) = RustM.ok (0 : i64) := by
  native_decide

theorem fibfib_at_one :
    clever_049_fibfib.fibfib (1 : i64) = RustM.ok (0 : i64) := by
  native_decide

theorem fibfib_at_two :
    clever_049_fibfib.fibfib (2 : i64) = RustM.ok (1 : i64) := by
  native_decide

theorem fibfib_at_three :
    clever_049_fibfib.fibfib (3 : i64) = RustM.ok (1 : i64) := by
  native_decide

theorem fibfib_at_four :
    clever_049_fibfib.fibfib (4 : i64) = RustM.ok (2 : i64) := by
  native_decide

theorem fibfib_at_five :
    clever_049_fibfib.fibfib (5 : i64) = RustM.ok (4 : i64) := by
  native_decide

theorem fibfib_at_six :
    clever_049_fibfib.fibfib (6 : i64) = RustM.ok (7 : i64) := by
  native_decide

/-! ## Negative-input sentinel (from `negative_inputs_are_zero`)

The `negative_inputs_are_zero` proptest asserts `fibfib(n) = 0` for
every `n < 0`. This is the function's "out-of-domain" sentinel branch
in the public wrapper. We bridge the `n <? 0` Bool guard via
`Int64.lt_iff_toInt_lt` and discharge the resulting `if` by `rfl`. -/

theorem fibfib_negative_returns_zero (n : i64) (h : n.toInt < 0) :
    clever_049_fibfib.fibfib n = RustM.ok (0 : i64) := by
  unfold clever_049_fibfib.fibfib
  have h_lt : decide (n < (0 : i64)) = true := by
    rw [decide_eq_true_iff, Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact h
  simp only [rust_primitives.cmp.lt, h_lt, pure_bind, ↓reduceIte]
  rfl

/-! ## Linear recurrence on the safe nonneg range (from
    `recurrence_on_nonneg_range`)

The `recurrence_on_nonneg_range` proptest asserts, for `n ∈ [3, 60]`,
that `fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)`. The bound
`n ≤ 60` keeps every intermediate value well below the i64 overflow
threshold (`fibfib` grows ≈ 1.84^n; i64 fits up to roughly `n = 75`). -/

/-! ## Helpers for the linear recurrence

The recurrence is proved by projecting `n` to a `Nat` index
`k = n.toInt.toNat ∈ [3, 60]`, then bridging to an iteratively-defined
`Nat → Int` oracle `fibfib_oracle`.  The naive 3-way recursion is
exponential and intractable for `native_decide`; iteration is O(k). -/

/-- Tail-recursive accumulator for `fibfib_oracle`: mirrors the Rust
    `fibfib_at`'s 3-window slide, computing each value in O(n) steps. -/
private def fibfib_oracle_aux : Nat → Int → Int → Int → Int
  | 0,     a, _, _ => a
  | n + 1, a, b, c => fibfib_oracle_aux n b c (a + b + c)

/-- Mathematical 3-step Fibonacci: matches the `fibfib_at` sliding
    window's interpretation on the safe nonneg range.  Implemented
    iteratively so `fibfib_oracle k` evaluates in O(k). -/
private def fibfib_oracle (n : Nat) : Int :=
  fibfib_oracle_aux n 0 0 1

/-- Overflow bound on `fibfib_oracle` over `[0, 63]`: every value fits
    in i64.  Used by `fibfib_oracle_toInt_ofInt`.  Proved by a single
    `native_decide` — fast because `fibfib_oracle` is iterative. -/
private theorem fibfib_oracle_bounded :
    ∀ k : Nat, k ≤ 63 →
      -(2^63 : Int) ≤ fibfib_oracle k ∧ fibfib_oracle k < 2^63 := by
  native_decide

/-- Bundled equivalence: for every `k ∈ [0, 60]`, `fibfib` on the i64
    lift of `k` succeeds with value `Int64.ofInt (fibfib_oracle k)`.
    Proved by a single `native_decide` so all 61 cases share one native
    compile/link cycle. -/
private theorem fibfib_eq_oracle :
    ∀ k : Nat, k ≤ 60 →
      clever_049_fibfib.fibfib (Int64.ofNat k) =
        RustM.ok (Int64.ofInt (fibfib_oracle k)) := by
  native_decide

/-- Mathematical recurrence at the oracle level, over `[0, 60]`:
    `fibfib_oracle (k+3) = fibfib_oracle (k+2) + fibfib_oracle (k+1) +
                            fibfib_oracle k`. -/
private theorem fibfib_oracle_rec :
    ∀ k : Nat, k ≤ 60 →
      fibfib_oracle (k + 3) =
        fibfib_oracle (k + 2) + fibfib_oracle (k + 1) + fibfib_oracle k := by
  native_decide

/-- i64 subtraction by a small `Nat` literal commutes with `Int64.ofNat`
    on the safe range.  For `m ∈ [0, 57]`, with `k := m + 3 ∈ [3, 60]`,
    `Int64.ofNat k - j = Int64.ofNat (k - j)` for each `j ∈ {1,2,3}`. -/
private theorem int64_ofNat_sub :
    ∀ m : Nat, m < 58 →
      (Int64.ofNat (m + 3) - 1 : i64) = Int64.ofNat (m + 3 - 1) ∧
      (Int64.ofNat (m + 3) - 2 : i64) = Int64.ofNat (m + 3 - 2) ∧
      (Int64.ofNat (m + 3) - 3 : i64) = Int64.ofNat (m + 3 - 3) := by
  native_decide

/-- The `.toInt` round-trip on `Int64.ofInt (fibfib_oracle k)` for
    `k ∈ [0, 63]`: extracts the underlying `Int` back unchanged because
    the value fits in i64. -/
private theorem fibfib_oracle_toInt_ofInt
    (k : Nat) (h : k ≤ 63) :
    (Int64.ofInt (fibfib_oracle k) : i64).toInt = fibfib_oracle k := by
  have ⟨hlo, hhi⟩ := fibfib_oracle_bounded k h
  exact Int64.toInt_ofInt_of_le hlo hhi

/-- Linear recurrence on the safe nonneg range `[3, 60]`:
    `fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)` (under
    `.toInt`).  Proof projects `n` to `k := n.toInt.toNat`, shifts to
    `m := k - 3`, applies the bridging lemmas, and closes with the
    oracle-level recurrence. -/
theorem fibfib_recurrence
    (n : i64) (h_lo : 3 ≤ n.toInt) (h_hi : n.toInt ≤ 60) :
    ∃ v vm1 vm2 vm3 : i64,
      clever_049_fibfib.fibfib n       = RustM.ok v ∧
      clever_049_fibfib.fibfib (n - 1) = RustM.ok vm1 ∧
      clever_049_fibfib.fibfib (n - 2) = RustM.ok vm2 ∧
      clever_049_fibfib.fibfib (n - 3) = RustM.ok vm3 ∧
      v.toInt = vm1.toInt + vm2.toInt + vm3.toInt := by
  -- Step 1: Project n to a `Nat` index k = n.toInt.toNat ∈ [3, 60].
  let k : Nat := n.toInt.toNat
  let m : Nat := k - 3
  have h_k_ge_3 : 3 ≤ k := by show 3 ≤ n.toInt.toNat; omega
  have h_k_le_60 : k ≤ 60 := by show n.toInt.toNat ≤ 60; omega
  -- Step 2: Shift to m = k - 3.
  have h_m_lt : m < 58 := by show k - 3 < 58; omega
  have h_k_eq_m : k = m + 3 := by show k = (k - 3) + 3; omega
  -- Step 3: n = Int64.ofNat k.
  have h_n_eq : n = Int64.ofNat k := by
    have h_int_eq : (k : Int) = n.toInt := by
      show (n.toInt.toNat : Int) = n.toInt; omega
    have h_ofInt : Int64.ofInt n.toInt = n := Int64.ofInt_eq_of_toInt_eq rfl
    show n = Int64.ofInt (k : Int)
    rw [h_int_eq]; exact h_ofInt.symm
  -- Step 4: n - j = Int64.ofNat (k - j) for j ∈ {1, 2, 3}.
  obtain ⟨h_sub1, h_sub2, h_sub3⟩ := int64_ofNat_sub m h_m_lt
  have h_km1 : k - 1 = m + 3 - 1 := by rw [h_k_eq_m]
  have h_km2 : k - 2 = m + 3 - 2 := by rw [h_k_eq_m]
  have h_km3 : k - 3 = m + 3 - 3 := by rw [h_k_eq_m]
  -- Step 5: Apply `fibfib_eq_oracle` at k, k-1, k-2, k-3.
  have h_fib_k  : clever_049_fibfib.fibfib (Int64.ofNat k) =
                    RustM.ok (Int64.ofInt (fibfib_oracle k)) :=
    fibfib_eq_oracle k h_k_le_60
  have h_fib_m1 : clever_049_fibfib.fibfib (Int64.ofNat (k - 1)) =
                    RustM.ok (Int64.ofInt (fibfib_oracle (k - 1))) :=
    fibfib_eq_oracle (k - 1) (by omega)
  have h_fib_m2 : clever_049_fibfib.fibfib (Int64.ofNat (k - 2)) =
                    RustM.ok (Int64.ofInt (fibfib_oracle (k - 2))) :=
    fibfib_eq_oracle (k - 2) (by omega)
  have h_fib_m3 : clever_049_fibfib.fibfib (Int64.ofNat (k - 3)) =
                    RustM.ok (Int64.ofInt (fibfib_oracle (k - 3))) :=
    fibfib_eq_oracle (k - 3) (by omega)
  -- Step 6: toInt round-trips for each witness.
  have h_t_k  := fibfib_oracle_toInt_ofInt k       (by omega)
  have h_t_m1 := fibfib_oracle_toInt_ofInt (k - 1) (by omega)
  have h_t_m2 := fibfib_oracle_toInt_ofInt (k - 2) (by omega)
  have h_t_m3 := fibfib_oracle_toInt_ofInt (k - 3) (by omega)
  -- Step 7: Oracle-level recurrence at index k.
  have h_rec : fibfib_oracle k =
      fibfib_oracle (k - 1) + fibfib_oracle (k - 2) + fibfib_oracle (k - 3) := by
    rw [h_k_eq_m]
    show fibfib_oracle (m + 3) =
         fibfib_oracle (m + 3 - 1) + fibfib_oracle (m + 3 - 2) +
         fibfib_oracle (m + 3 - 3)
    show fibfib_oracle (m + 3) =
         fibfib_oracle (m + 2) + fibfib_oracle (m + 1) + fibfib_oracle m
    exact fibfib_oracle_rec m (by omega)
  -- Step 8: Take witnesses and discharge each conjunct.
  refine ⟨Int64.ofInt (fibfib_oracle k),
          Int64.ofInt (fibfib_oracle (k - 1)),
          Int64.ofInt (fibfib_oracle (k - 2)),
          Int64.ofInt (fibfib_oracle (k - 3)),
          ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_n_eq]; exact h_fib_k
  · rw [h_n_eq, h_k_eq_m, h_sub1, ← h_km1]; exact h_fib_m1
  · rw [h_n_eq, h_k_eq_m, h_sub2, ← h_km2]; exact h_fib_m2
  · rw [h_n_eq, h_k_eq_m, h_sub3, ← h_km3]; exact h_fib_m3
  · rw [h_t_k, h_t_m1, h_t_m2, h_t_m3]; exact h_rec

end Clever_049_fibfibObligations
