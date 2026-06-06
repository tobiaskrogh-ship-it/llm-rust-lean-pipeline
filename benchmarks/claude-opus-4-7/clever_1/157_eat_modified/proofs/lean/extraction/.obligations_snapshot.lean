-- Companion obligations file for the `clever_157_eat` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_157_eat

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_157_eatObligations

/-! ## Contract clauses for `eat`.

The Rust source builds a fixed 2-element `Vec u64` via `extend_from_slice`
of a typed `[u64; 2]` chunk onto a freshly-allocated `Vec::new()`. The
function performs at most one of `number +? need`, `remaining -? need`,
`number +? remaining`, which never fail provided the corresponding
sums fit in `u64`. The proptests bound all inputs to `< 1_000_000`, but
the natural Lean precondition is the no-overflow bound on the two sums
that actually appear (`number + need` in the take branch, `number +
remaining` in the skip branch). We assume both throughout to keep the
preconditions uniform across branches.

Each contract-style proptest in the Rust source becomes one independent
`theorem`. The proofs are deferred to the proof stage (`sorry`). -/

/-- Length: the returned vector always has exactly two elements.
    Corresponds to Rust proptest `length_is_two`. -/
theorem eat_length_is_two
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      v.val.size = 2 := by
  sorry

/-- Conservation: the two output slots sum to `number + remaining`
    (taken at the `Nat` level so the equation is well-formed even when
    `r[0]` could itself approach the `u64` boundary).
    Corresponds to Rust proptest `conservation`. -/
theorem eat_conservation
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size) (h1 : 1 < v.val.size),
        (v.val[0]'h0).toNat + (v.val[1]'h1).toNat
          = number.toNat + remaining.toNat := by
  sorry

/-- Monotonicity in the first slot: you never "un-eat" — the total eaten
    after the call is at least the count from before.
    Corresponds to the first sub-clause of Rust proptest `eat_at_most_need`
    (`r[0] >= number`). -/
theorem eat_first_at_least_number
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size),
        number.toNat ≤ (v.val[0]'h0).toNat := by
  sorry

/-- Bounded appetite: you eat at most `need` carrots this round.
    Corresponds to the second sub-clause of Rust proptest
    `eat_at_most_need` (`r[0] - number <= need`). -/
theorem eat_diff_le_need
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size),
        (v.val[0]'h0).toNat - number.toNat ≤ need.toNat := by
  sorry

/-- Maximality: either the full `need` was satisfied, or no carrots are
    left.
    Corresponds to Rust proptest `sated_or_finished`. -/
theorem eat_sated_or_finished
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size) (h1 : 1 < v.val.size),
        (v.val[0]'h0).toNat = number.toNat + need.toNat ∨
        (v.val[1]'h1).toNat = 0 := by
  sorry

end Clever_157_eatObligations
