-- Companion obligations file for the `clever_122_get_odd_collatz` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_122_get_odd_collatz

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_122_get_odd_collatzObligations

/-! ## Specification oracles for the postconditions.

The Rust source phrases its three contract-style proptests via two
auxiliary notions: (i) strict ascending order on the result vector, and
(ii) reachability under the Collatz step relation. We mirror both at
the `Nat` level so the obligations are independent of the
implementation under verification. -/

/-- Strictly ascending order on a `u64` array. Matches the proptest
    `prop_sorted_strictly_ascending`, which checks `r[i-1] < r[i]`. -/
private def strict_asc (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ < k₂ → (arr[k₁]'h₁).toNat < (arr[k₂]'h₂).toNat

/-- One Collatz step on `Nat`. Matches the iteration body of the Rust
    `step_at` (and of the `reference` oracle in the test): `x/2` if `x`
    is even, `3 * x + 1` otherwise. -/
private def collatz_step (x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else 3 * x + 1

/-- Apply `collatz_step` `k` times. -/
private def collatz_iter : Nat → Nat → Nat
  | 0,     x => x
  | k + 1, x => collatz_iter k (collatz_step x)

/-- `v` is reachable from `n` via some finite number of Collatz steps. -/
private def collatz_reachable (n v : Nat) : Prop :=
  ∃ k : Nat, collatz_iter k n = v

/-! ## Unit pins.

The Rust source includes three exact-input tests:
  * `zero_is_empty`  — `get_odd_collatz(0) = []`.
  * `known`          — `get_odd_collatz(1) = [1]` and `get_odd_collatz(5) = [1, 5]`.

Note(termination): `step_at` is extracted with `partial_fixpoint` since
total termination of the Collatz iteration is an open conjecture. The
function is nonetheless computable end-to-end on any concrete input
whose orbit reaches `1`: `native_decide` evaluates the fixpoint kernel
by kernel, threading `RustM` through each step. -/

/-- Anchor pin (from `zero_is_empty`): the empty input yields the empty
    vector. The `n = 0` branch short-circuits before `step_at`, so this
    holds independently of the partial-fixpoint termination. Stated
    existentially because `alloc.vec.Vec u64 _` is a Subtype carrying a
    proof component, so `DecidableEq` does not auto-derive cleanly. -/
theorem get_odd_collatz_zero_is_empty :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (0 : u64) = RustM.ok v
      ∧ v.val.toList = [] := by
  sorry

/-- Unit pin (from `known`): `get_odd_collatz(1) = [1]`. -/
theorem get_odd_collatz_at_one :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (1 : u64) = RustM.ok v
      ∧ v.val.toList = [(1 : u64)] := by
  sorry

/-- Unit pin (from `known`): `get_odd_collatz(5) = [1, 5]`. -/
theorem get_odd_collatz_at_five :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (5 : u64) = RustM.ok v
      ∧ v.val.toList = [(1 : u64), (5 : u64)] := by
  sorry

/-! ## Universal contract clauses (proptests).

The three proptests phrase universal claims over `n in 1u64..=10_000`.
Because `step_at` is `partial_fixpoint`, total universal claims (over
all `u64`) cannot be proven without resolving Collatz: for any `n` whose
orbit fails to reach `1`, the function may not return `RustM.ok` at
all. We thread the implicit "the function returns ok" hypothesis
through every universal clause via `hres : ... = RustM.ok v`, which is
the natural and strongest honest postcondition shape.

(Note: for the proptest range `n.toNat ≤ 10_000`, the orbit is known
to terminate within `u64`; `hres` is then discharged. The proof stage
may add this bound where convenient.) -/

/-- Postcondition (from the proptest `prop_sorted_strictly_ascending`):
    whenever `get_odd_collatz n` succeeds, the result is strictly
    ascending. Captures both sortedness and uniqueness in one check —
    if either failed, the proptest would too. -/
theorem get_odd_collatz_strict_asc (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v) :
    strict_asc v.val := by
  sorry

/-- Postcondition (from the proptest `prop_all_elements_odd`):
    whenever `get_odd_collatz n` succeeds, every element of the output
    is odd. -/
theorem get_odd_collatz_all_odd (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    (v.val[k]'hk).toNat % 2 = 1 := by
  sorry

/-- Postcondition (from the proptest `prop_matches_reference`, soundness
    half): every output element is Collatz-reachable from `n.toNat`.
    Combined with `get_odd_collatz_all_odd`, this means every output
    element is an odd value lying on the orbit of `n`. -/
theorem get_odd_collatz_output_reachable (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    collatz_reachable n.toNat (v.val[k]'hk).toNat := by
  sorry

/-- Postcondition (from the proptest `prop_matches_reference`,
    completeness half): every odd value `w < 2^64` that is
    Collatz-reachable from `n.toNat` appears as some output element.

    Bound `w < 2^64` is required so that `w` can be stored in a `u64`
    cell of the output. -/
theorem get_odd_collatz_reachable_odd_in_output (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (w : Nat) (hreach : collatz_reachable n.toNat w)
    (hodd : w % 2 = 1) (hwlt : w < 2 ^ 64) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), (v.val[k]'hk).toNat = w := by
  sorry

end Clever_122_get_odd_collatzObligations
