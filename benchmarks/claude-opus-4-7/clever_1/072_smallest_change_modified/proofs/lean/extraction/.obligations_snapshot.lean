-- Companion obligations file for the `clever_072_smallest_change` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_072_smallest_change

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_072_smallest_changeObligations

/-! ## Specifications

`num_mismatches arr i` counts mirror-pair mismatches `(arr[k], arr[n-1-k])`
for indices `k ∈ [i, n/2)`, expressed at the `Nat` level. Since the slice
size `n < 2^64` and the count is bounded by `n/2 < 2^63`, the result always
fits in `i64`, so the Lean statement can be universal without preconditions.

`is_palindrome arr` says every mirror pair `(arr[i], arr[n-1-i])` is equal. -/

private def num_mismatches (arr : RustSlice i64) (i : Nat) : Nat :=
  if h : i < arr.val.size / 2 then
    have hi : i < arr.val.size := Nat.lt_of_lt_of_le h (Nat.div_le_self _ _)
    have hmirror : arr.val.size - 1 - i < arr.val.size := by
      have : 0 < arr.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
      omega
    (if arr.val[i]'hi ≠ arr.val[arr.val.size - 1 - i]'hmirror then 1 else 0) +
      num_mismatches arr (i + 1)
  else 0
termination_by arr.val.size / 2 - i

private def is_palindrome (arr : RustSlice i64) : Prop :=
  ∀ i : Nat, i < arr.val.size / 2 →
    ∀ (hi : i < arr.val.size) (hmirror : arr.val.size - 1 - i < arr.val.size),
      arr.val[i]'hi = arr.val[arr.val.size - 1 - i]'hmirror

/-! ## Top-level contract clauses -/

/-- Functional correctness against the reference oracle: `smallest_change`
    returns a successful `i64` whose integer value equals the count of
    mismatched mirror pairs. Encodes the `matches_brute_force` proptest. -/
theorem matches_brute_force (arr : RustSlice i64) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr = RustM.ok r ∧
      r.toInt = (num_mismatches arr 0 : Int) := by
  sorry

/-- Zero-iff-palindrome: the function returns `0` exactly when the input is
    already a palindrome. Encodes the `zero_iff_palindrome` proptest. -/
theorem zero_iff_palindrome (arr : RustSlice i64) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr = RustM.ok r ∧
      (r = 0 ↔ is_palindrome arr) := by
  sorry

/-- Reversal invariance: if `arr2` is the mirror of `arr1` (same length and
    `arr2[n-1-i] = arr1[i]` for every valid `i`), the function returns the
    same result on both inputs. Encodes the `reverse_invariant` proptest. -/
theorem reverse_invariant (arr1 arr2 : RustSlice i64)
    (hsize : arr1.val.size = arr2.val.size)
    (hrev : ∀ i : Nat, ∀ (hi1 : i < arr1.val.size)
              (hi2 : arr2.val.size - 1 - i < arr2.val.size),
              arr2.val[arr2.val.size - 1 - i]'hi2 = arr1.val[i]'hi1) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr1 = RustM.ok r ∧
      clever_072_smallest_change.smallest_change arr2 = RustM.ok r := by
  sorry

end Clever_072_smallest_changeObligations
