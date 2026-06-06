-- Companion obligations file for the `clever_062_fibfib` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_062_fibfib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_062_fibfibObligations

/-! ## Base cases — unit pins

The Rust `base_cases` test asserts three specific seed values:
`fibfib(0) = 0`, `fibfib(1) = 0`, `fibfib(2) = 1`. Each is one
independent contract clause; together they pin the seed of the 3-window
sliding recurrence and forbid trivial (all-zero or shifted)
implementations from satisfying the rest of the contract.

`fibfib_at` is extracted via `partial_fixpoint`, but the function is
computable end-to-end for small inputs: `native_decide` evaluates the
fixpoint kernel by kernel, threading `RustM` through each iterative
step. -/

/-- Unit pin (`base_cases`): `fibfib(0) = 0`. -/
theorem fibfib_zero :
    clever_062_fibfib.fibfib (0 : u64) = RustM.ok (0 : u64) := by
  native_decide

/-- Unit pin (`base_cases`): `fibfib(1) = 0`. -/
theorem fibfib_one :
    clever_062_fibfib.fibfib (1 : u64) = RustM.ok (0 : u64) := by
  native_decide

/-- Unit pin (`base_cases`): `fibfib(2) = 1`. -/
theorem fibfib_two :
    clever_062_fibfib.fibfib (2 : u64) = RustM.ok (1 : u64) := by
  native_decide

/-! ## Linear recurrence on the safe nonneg range

The `recurrence` proptest asserts, for `n ∈ [3, 60]`, that
`fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)`.  The bound
`n.toNat ≤ 60` keeps every intermediate value well below the u64
overflow threshold (`fibfib` grows ≈ 1.84^n; u64 fits up to
roughly n ≈ 87, since 1.84^87 ≈ 2^64).

We package the recurrence as: in the safe range, all four calls
succeed and the `Nat`-valued results satisfy the recurrence on
`.toNat`. The `.toNat` formulation matches the no-overflow regime:
in the safe range `[3, 60]`, the Rust wrapping u64 addition
coincides with the `Nat` addition the test pretends to compute. -/

/-! ## Helpers for the linear recurrence

The recurrence is proved by enumerating `n` over the bounded range
`[3, 60]`.  For each concrete value, `native_decide` evaluates the
`fibfib` call and additive constraint by computation through the
`partial_fixpoint` kernel.  The conversion from `n.toNat ∈ [3, 60]` to
`n = UInt64.ofNat k` for a concrete `k` is via `UInt64.ofNat_eq_of_toNat_eq`.
The witnesses are provided as `UInt64.ofNat (fibfib_oracle k)` — the
mathematical 3-step Fibonacci computed by Lean, avoiding manual literal
computation of f(58), f(59), f(60). -/

/-- Tail-recursive accumulator for `fibfib_oracle`: mirrors the Rust
    `fibfib_at`'s 3-window slide, computing each value in O(n) steps. -/
private def fibfib_oracle_aux : Nat → Nat → Nat → Nat → Nat
  | 0,     a, _, _ => a
  | n + 1, a, b, c => fibfib_oracle_aux n b c (a + b + c)

/-- Mathematical 3-step Fibonacci: matches the `fibfib_at` sliding window's
    interpretation on the safe nonneg range.  Implemented iteratively so
    `fibfib_oracle k` evaluates in O(k). -/
private def fibfib_oracle (n : Nat) : Nat :=
  fibfib_oracle_aux n 0 0 1

/-- Overflow bound on `fibfib_oracle` over `[0, 63]`: every value fits in u64.
    Proved by a single `native_decide` — fast because `fibfib_oracle` is
    iterative (O(n)) and no `partial_fixpoint` evaluation is involved. -/
private theorem fibfib_oracle_bounded :
    ∀ k : Nat, k ≤ 63 → fibfib_oracle k < 2 ^ 64 := by
  native_decide

/-- Bridge `UInt64.ofNat x` toNat for `x < 2^64`. -/
private theorem u64_ofNat_toNat_of_lt (x : Nat) (h : x < 2 ^ 64) :
    (UInt64.ofNat x).toNat = x := by
  simp [UInt64.toNat, UInt64.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The `.toNat` round-trip on `UInt64.ofNat (fibfib_oracle k)` for k ≤ 63. -/
private theorem fibfib_oracle_toNat_ofNat
    (k : Nat) (h : k ≤ 63) :
    (UInt64.ofNat (fibfib_oracle k) : u64).toNat = fibfib_oracle k :=
  u64_ofNat_toNat_of_lt _ (fibfib_oracle_bounded k h)

/-- Bundled equivalence: for every `k ∈ [0, 60]`, `fibfib` on the u64 lift of
    `k` succeeds with value `UInt64.ofNat (fibfib_oracle k)`.  Proved by a
    single `native_decide` so all 61 cases share one native compile/link
    cycle. -/
private theorem fibfib_eq_oracle :
    ∀ k : Nat, k ≤ 60 →
      clever_062_fibfib.fibfib (UInt64.ofNat k) =
        RustM.ok (UInt64.ofNat (fibfib_oracle k)) := by
  native_decide

/-- Mathematical recurrence at the oracle level, over `[0, 57]`:
    `fibfib_oracle (k+3) = fibfib_oracle (k+2) + fibfib_oracle (k+1) +
                           fibfib_oracle k`. -/
private theorem fibfib_oracle_rec :
    ∀ k : Nat, k ≤ 57 →
      fibfib_oracle (k + 3) =
        fibfib_oracle (k + 2) + fibfib_oracle (k + 1) + fibfib_oracle k := by
  native_decide

/-- u64 subtraction by a small `Nat` literal commutes with `UInt64.ofNat`
    on the safe range.  For `m ∈ [0, 57]`, with `k := m + 3 ∈ [3, 60]`,
    `UInt64.ofNat k - j = UInt64.ofNat (k - j)` for each `j ∈ {1, 2, 3}`
    since no underflow occurs. -/
private theorem uint64_ofNat_sub :
    ∀ m : Nat, m < 58 →
      (UInt64.ofNat (m + 3) - 1 : u64) = UInt64.ofNat (m + 3 - 1) ∧
      (UInt64.ofNat (m + 3) - 2 : u64) = UInt64.ofNat (m + 3 - 2) ∧
      (UInt64.ofNat (m + 3) - 3 : u64) = UInt64.ofNat (m + 3 - 3) := by
  native_decide

/-- Linear recurrence on the safe nonneg range `[3, 60]`:
    `fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)` (under
    `.toNat`).

    The proof projects `n` to a `Nat` index `k := n.toNat ∈ [3, 60]`,
    shifts to `m := k - 3 ∈ [0, 57]` so `uint64_ofNat_sub` applies,
    derives `n = UInt64.ofNat k` from `UInt64.ofNat_eq_of_toNat_eq`,
    converts each `n - j` into `UInt64.ofNat (k - j)` for `j ∈ {1, 2, 3}`,
    applies `fibfib_eq_oracle` at `k, k-1, k-2, k-3` to pull each
    `fibfib (UInt64.ofNat _)` value back to `UInt64.ofNat (fibfib_oracle _)`,
    then closes the `.toNat` additive identity via `fibfib_oracle_toNat_ofNat`
    (each round-trip preserves the value because `fibfib_oracle_bounded`
    shows it fits in u64) and `fibfib_oracle_rec` (the mathematical
    recurrence at the oracle level). -/
theorem fibfib_recurrence
    (n : u64) (h_lo : 3 ≤ n.toNat) (h_hi : n.toNat ≤ 60) :
    ∃ v vm1 vm2 vm3 : u64,
      clever_062_fibfib.fibfib n       = RustM.ok v ∧
      clever_062_fibfib.fibfib (n - 1) = RustM.ok vm1 ∧
      clever_062_fibfib.fibfib (n - 2) = RustM.ok vm2 ∧
      clever_062_fibfib.fibfib (n - 3) = RustM.ok vm3 ∧
      v.toNat = vm1.toNat + vm2.toNat + vm3.toNat := by
  -- Step 1: Project n to a `Nat` index `k = n.toNat` with k ∈ [3, 60].
  let k : Nat := n.toNat
  let m : Nat := k - 3
  have h_k_ge_3 : 3 ≤ k := h_lo
  have h_k_le_60 : k ≤ 60 := h_hi
  -- Step 2: Shift to `m = k - 3`.
  have h_m_lt : m < 58 := by show k - 3 < 58; omega
  have h_k_eq_m : k = m + 3 := by show k = (k - 3) + 3; omega
  -- Step 3: n = UInt64.ofNat k.
  have h_n_eq : n = UInt64.ofNat k := (UInt64.ofNat_eq_of_toNat_eq rfl).symm
  -- Step 4: n - j = UInt64.ofNat (k - j) for j ∈ {1, 2, 3}.
  obtain ⟨h_sub1, h_sub2, h_sub3⟩ := uint64_ofNat_sub m h_m_lt
  have h_km1 : k - 1 = m + 3 - 1 := by rw [h_k_eq_m]
  have h_km2 : k - 2 = m + 3 - 2 := by rw [h_k_eq_m]
  have h_km3 : k - 3 = m + 3 - 3 := by rw [h_k_eq_m]
  -- Step 5: Apply `fibfib_eq_oracle` at k, k-1, k-2, k-3.
  have h_fib_k  : clever_062_fibfib.fibfib (UInt64.ofNat k) =
                    RustM.ok (UInt64.ofNat (fibfib_oracle k)) :=
    fibfib_eq_oracle k h_k_le_60
  have h_fib_m1 : clever_062_fibfib.fibfib (UInt64.ofNat (k - 1)) =
                    RustM.ok (UInt64.ofNat (fibfib_oracle (k - 1))) :=
    fibfib_eq_oracle (k - 1) (by omega)
  have h_fib_m2 : clever_062_fibfib.fibfib (UInt64.ofNat (k - 2)) =
                    RustM.ok (UInt64.ofNat (fibfib_oracle (k - 2))) :=
    fibfib_eq_oracle (k - 2) (by omega)
  have h_fib_m3 : clever_062_fibfib.fibfib (UInt64.ofNat (k - 3)) =
                    RustM.ok (UInt64.ofNat (fibfib_oracle (k - 3))) :=
    fibfib_eq_oracle (k - 3) (by omega)
  -- Step 6: toNat round-trips for each witness.
  have h_t_k  := fibfib_oracle_toNat_ofNat k       (by omega)
  have h_t_m1 := fibfib_oracle_toNat_ofNat (k - 1) (by omega)
  have h_t_m2 := fibfib_oracle_toNat_ofNat (k - 2) (by omega)
  have h_t_m3 := fibfib_oracle_toNat_ofNat (k - 3) (by omega)
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
  refine ⟨UInt64.ofNat (fibfib_oracle k),
          UInt64.ofNat (fibfib_oracle (k - 1)),
          UInt64.ofNat (fibfib_oracle (k - 2)),
          UInt64.ofNat (fibfib_oracle (k - 3)),
          ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_n_eq]; exact h_fib_k
  · rw [h_n_eq, h_k_eq_m, h_sub1, ← h_km1]; exact h_fib_m1
  · rw [h_n_eq, h_k_eq_m, h_sub2, ← h_km2]; exact h_fib_m2
  · rw [h_n_eq, h_k_eq_m, h_sub3, ← h_km3]; exact h_fib_m3
  · rw [h_t_k, h_t_m1, h_t_m2, h_t_m3]; exact h_rec

end Clever_062_fibfibObligations
