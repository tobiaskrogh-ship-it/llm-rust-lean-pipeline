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
  sorry

theorem fib_at_1 :
    clever_054_fib.fib (1 : u64) = RustM.ok (1 : u64) := by
  sorry

theorem fib_at_2 :
    clever_054_fib.fib (2 : u64) = RustM.ok (1 : u64) := by
  sorry

theorem fib_at_3 :
    clever_054_fib.fib (3 : u64) = RustM.ok (2 : u64) := by
  sorry

theorem fib_at_4 :
    clever_054_fib.fib (4 : u64) = RustM.ok (3 : u64) := by
  sorry

theorem fib_at_5 :
    clever_054_fib.fib (5 : u64) = RustM.ok (5 : u64) := by
  sorry

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

/-- Linear recurrence on the safe range `[2, 92]`:
    `fib(n) = fib(n-1) + fib(n-2)` (under `.toNat`, no wrap-around). -/
theorem fib_recurrence
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat ≤ 92) :
    ∃ v vm1 vm2 : u64,
      clever_054_fib.fib n       = RustM.ok v ∧
      clever_054_fib.fib (n - 1) = RustM.ok vm1 ∧
      clever_054_fib.fib (n - 2) = RustM.ok vm2 ∧
      v.toNat = vm1.toNat + vm2.toNat := by
  sorry

end Clever_054_fibObligations
