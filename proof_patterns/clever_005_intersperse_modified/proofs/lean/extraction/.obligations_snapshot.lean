-- Companion obligations file for the `clever_005_intersperse` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_005_intersperse

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_005_intersperseObligations

-- Postcondition clause 1 (length):
--   • empty input → empty output;
--   • non-empty input of size n → output of size `2 * n - 1`.
-- Precondition: each `extend_from_slice` requires the running length plus
-- the chunk size to stay below `USize64.size`. The largest such check is
-- the final extend with a 2-element chunk, which needs `2 * s.val.size ≤
-- USize64.size`. Without this bound the function panics with
-- `maximumSizeExceeded` on the universal model, so the universal length
-- equation is false outside the bound.
theorem intersperse_length (s : RustSlice i64) (delim : i64) :
    ⦃ ⌜ 2 * s.val.size ≤ USize64.size ⌝ ⦄
    clever_005_intersperse.intersperse s delim
    ⦃ ⇓ r => ⌜ r.val.size = if s.val.size = 0 then 0 else 2 * s.val.size - 1 ⌝ ⦄ := by
  sorry

-- Postcondition clause 2 (even indices preserve the input in order):
--   for every `i < s.val.size`, `result[2 * i] = s[i]`.
-- We phrase the index equality via `Array.getElem?` so the in-bounds
-- condition on the result is implied by the equality.
theorem intersperse_even_indices_original (s : RustSlice i64) (delim : i64) :
    ⦃ ⌜ 2 * s.val.size ≤ USize64.size ⌝ ⦄
    clever_005_intersperse.intersperse s delim
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < s.val.size → r.val[2 * i]? = s.val[i]? ⌝ ⦄ := by
  sorry

-- Postcondition clause 3 (odd indices are the delimiter):
--   for every `i + 1 < s.val.size`, `result[2 * i + 1] = delimiter`.
theorem intersperse_odd_indices_delim (s : RustSlice i64) (delim : i64) :
    ⦃ ⌜ 2 * s.val.size ≤ USize64.size ⌝ ⦄
    clever_005_intersperse.intersperse s delim
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i + 1 < s.val.size → r.val[2 * i + 1]? = some delim ⌝ ⦄ := by
  sorry

end Clever_005_intersperseObligations
