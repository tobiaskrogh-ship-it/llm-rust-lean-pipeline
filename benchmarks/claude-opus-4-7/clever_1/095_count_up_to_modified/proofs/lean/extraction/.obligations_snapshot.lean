-- Companion obligations file for the `clever_095_count_up_to` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_095_count_up_to

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_095_count_up_toObligations

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Main contract clauses -/

/-- Boundary clause: when `n < 2`, the result is the empty `Vec`.
    Captures the Rust property test `empty_below_two`. -/
theorem empty_below_two
    (n : u64) (h : n.toNat < 2) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_095_count_up_to.count_up_to n = RustM.ok v ∧ v.val.size = 0 := by
  sorry

/-- Soundness clause: every element of the returned `Vec` is prime.
    Captures the Rust property test `all_elements_prime`. -/
theorem all_elements_prime
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), is_prime_nat (v.val[k]'hk).toNat := by
  sorry

/-- Upper-bound clause: every element of the returned `Vec` is strictly
    less than `n`. Captures the Rust property test `all_elements_below_n`. -/
theorem all_elements_below_n
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat < n.toNat := by
  sorry

/-- Ordering clause: consecutive entries of the returned `Vec` are strictly
    increasing. Captures the Rust property test `strictly_ascending`. -/
theorem strictly_ascending
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    ∀ (k : Nat) (hk : k + 1 < v.val.size),
      (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat < (v.val[k + 1]'hk).toNat := by
  sorry

/-- Completeness clause: every prime in `[0, n)` appears in the returned
    `Vec`. Captures the Rust property test `complete`. -/
theorem complete
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v)
    (p : Nat) (hp_prime : is_prime_nat p) (hp_lt : p < n.toNat) :
    ∃ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat = p := by
  sorry

end Clever_095_count_up_toObligations
