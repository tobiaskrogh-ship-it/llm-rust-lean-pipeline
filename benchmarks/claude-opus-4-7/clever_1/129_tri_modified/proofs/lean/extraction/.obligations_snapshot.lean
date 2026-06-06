-- Companion obligations file for the `clever_129_tri` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_129_tri

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_129_triObligations

/-! ## Contract obligations for `clever_129_tri.tri`.

The Rust source contains four property-test clauses:

1. `length_is_n_plus_one` — the result has length `n + 1`.
2. `base_cases` — `r[0] = 3` and (when `n ≥ 1`) `r[1] = 3`.
3. `even_terms_closed_form` — for every even `i ≥ 2` with `i ≤ n`,
   `r[i] = 1 + i / 2`.
4. `odd_recurrence_holds` — for every odd `i ≥ 3` with `i + 1 ≤ n`,
   `r[i] = r[i-1] + r[i-2] + r[i+1]`.

Each clause becomes one theorem.  We do not impose a precondition on `n`
directly; instead each theorem is stated conditionally on the function
having succeeded (`tri n = RustM.ok v`).  This is the strongest honest
contract: large `n` causes the recursive tail call to overflow (`i + 1`
wraps once `n = u64::MAX`) or the odd-index value `(k+1)(k+3)` to exceed
`2^64`, so `tri n = ok v` is itself a non-trivial precondition for very
large `n`. -/

/-- Postcondition 1 (length): the result has length `n + 1`. -/
theorem tri_length
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v) :
    v.val.size = n.toNat + 1 := by
  sorry

/-- Postcondition 2a (base case at index 0): `r[0] = 3`. -/
theorem tri_index_zero
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (h0 : 0 < v.val.size) :
    (v.val[0]'h0).toNat = 3 := by
  sorry

/-- Postcondition 2b (base case at index 1): `r[1] = 3` when `n ≥ 1`. -/
theorem tri_index_one
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (h1 : 1 < v.val.size) :
    (v.val[1]'h1).toNat = 3 := by
  sorry

/-- Postcondition 3 (even closed form): for even `i ≥ 2` in range,
    `r[i] = 1 + i / 2`. -/
theorem tri_even_closed_form
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (i : Nat) (h_ge : 2 ≤ i) (h_even : i % 2 = 0)
    (hi : i < v.val.size) :
    (v.val[i]'hi).toNat = 1 + i / 2 := by
  sorry

/-- Postcondition 4 (odd recurrence): for odd `i ≥ 3` with `i + 1` in range,
    `r[i] = r[i-1] + r[i-2] + r[i+1]`. -/
theorem tri_odd_recurrence
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_129_tri.tri n = RustM.ok v)
    (i : Nat) (h_ge : 3 ≤ i) (h_odd : i % 2 = 1)
    (hi_p1 : i + 1 < v.val.size)
    (hi_lt : i < v.val.size)
    (hi_m1 : i - 1 < v.val.size)
    (hi_m2 : i - 2 < v.val.size) :
    (v.val[i]'hi_lt).toNat =
      (v.val[i - 1]'hi_m1).toNat
      + (v.val[i - 2]'hi_m2).toNat
      + (v.val[i + 1]'hi_p1).toNat := by
  sorry

end Clever_129_triObligations
