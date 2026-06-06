-- Companion obligations file for the `clever_108_move_one_ball` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_108_move_one_ball

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_108_move_one_ballObligations

/-! ## Specification: cyclic-rotation sortedness predicate.

`is_sorted_rotation arr k hk` says that rotating `arr` so the element at
index `k` becomes the new first element yields a non-decreasing sequence
(at the `i64` level).  Equivalently, every adjacent pair in the rotated
slice -- i.e. each pair `(arr[(i+k) mod n], arr[(i+1+k) mod n])` for
`i + 1 < n` -- is monotonically non-decreasing.

This is the Lean reflection of the property tests' `rotated`/`is_sorted`
duo: it ranges over exactly the family of right-rotations the algorithm
enumerates internally. -/
private def is_sorted_rotation
    (arr : RustSlice i64) (k : Nat) (hk : k < arr.val.size) : Prop :=
  ∀ i : Nat, ∀ (_hi1 : i + 1 < arr.val.size),
    arr.val[(i + k) % arr.val.size]'(Nat.mod_lt _ (by omega)) ≤
    arr.val[(i + 1 + k) % arr.val.size]'(Nat.mod_lt _ (by omega))

/-! ## Top-level contract clauses.

These mirror the three property tests in `src/lib.rs`:

* `empty_returns_true`            -> `move_one_ball_empty`
* `rotation_of_sorted_returns_true` -> `move_one_ball_complete`
* `true_implies_some_rotation_sorted` -> `move_one_ball_sound`
-/

/-- Boundary clause (`empty_returns_true`): the empty slice is always
    accepted. -/
theorem move_one_ball_empty (arr : RustSlice i64) (h : arr.val.size = 0) :
    clever_108_move_one_ball.move_one_ball arr = RustM.ok true := by
  sorry

/-- Completeness clause (`rotation_of_sorted_returns_true`): if some cyclic
    rotation of `arr` is sorted in non-decreasing order, then
    `move_one_ball arr` returns `true`.

    The size precondition `2 * arr.val.size < 2^64` ensures the internal
    `(i + k) %? n` and `(i + 1 + k) %? n` index computations do not
    overflow `usize`; without it, the universal claim is false in the
    Lean model for slices with `size ≥ 2^63` (the function then fails
    with `integerOverflow`). -/
theorem move_one_ball_complete
    (arr : RustSlice i64)
    (h_size : 2 * arr.val.size < 2 ^ 64)
    (h : ∃ k : Nat, ∃ (hk : k < arr.val.size), is_sorted_rotation arr k hk) :
    clever_108_move_one_ball.move_one_ball arr = RustM.ok true := by
  sorry

/-- Soundness clause (`true_implies_some_rotation_sorted`): if
    `move_one_ball arr` returns `true`, then either `arr` is empty, or
    some cyclic rotation of `arr` really is sorted in non-decreasing
    order.

    No size precondition is needed: on overflow the function returns
    `.fail .integerOverflow`, so the hypothesis becomes vacuously false. -/
theorem move_one_ball_sound
    (arr : RustSlice i64)
    (h : clever_108_move_one_ball.move_one_ball arr = RustM.ok true) :
    arr.val.size = 0 ∨
    ∃ k : Nat, ∃ (hk : k < arr.val.size), is_sorted_rotation arr k hk := by
  sorry

end Clever_108_move_one_ballObligations
