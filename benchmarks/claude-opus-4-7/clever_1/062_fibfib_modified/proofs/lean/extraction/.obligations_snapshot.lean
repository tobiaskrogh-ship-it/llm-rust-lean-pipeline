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
  sorry

/-- Unit pin (`base_cases`): `fibfib(1) = 0`. -/
theorem fibfib_one :
    clever_062_fibfib.fibfib (1 : u64) = RustM.ok (0 : u64) := by
  sorry

/-- Unit pin (`base_cases`): `fibfib(2) = 1`. -/
theorem fibfib_two :
    clever_062_fibfib.fibfib (2 : u64) = RustM.ok (1 : u64) := by
  sorry

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

/-- Linear recurrence on the safe nonneg range `[3, 60]`:
    `fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)` (under
    `.toNat`).  Captures the `recurrence` proptest. -/
theorem fibfib_recurrence
    (n : u64) (h_lo : 3 ≤ n.toNat) (h_hi : n.toNat ≤ 60) :
    ∃ v vm1 vm2 vm3 : u64,
      clever_062_fibfib.fibfib n       = RustM.ok v ∧
      clever_062_fibfib.fibfib (n - 1) = RustM.ok vm1 ∧
      clever_062_fibfib.fibfib (n - 2) = RustM.ok vm2 ∧
      clever_062_fibfib.fibfib (n - 3) = RustM.ok vm3 ∧
      v.toNat = vm1.toNat + vm2.toNat + vm3.toNat := by
  sorry

end Clever_062_fibfibObligations
