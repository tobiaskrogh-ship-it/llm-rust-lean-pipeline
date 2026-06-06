-- Companion obligations file for the `clever_150_compare` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_150_compare

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_150_compareObligations

/-- Length postcondition.

    When `compare s g` succeeds with output `v`, the length of `v` equals the
    minimum of the two input slice lengths.

    Corresponds to the proptest `length_is_min_of_inputs`. -/
theorem compare_length
    (s g : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_150_compare.compare s g = RustM.ok v) :
    v.val.size = min s.val.size g.val.size := by
  sorry

/-- Element-value postcondition.

    When `compare s g` succeeds with output `v`, for every output index `i`
    (which is also a valid index into both input slices, since the output
    length is `min s.size g.size`), the i-th output equals the absolute
    difference `|s[i] - g[i]|` interpreted as integers.

    Corresponds to the proptest `element_is_absolute_difference`. -/
theorem compare_element_is_abs_difference
    (s g : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_150_compare.compare s g = RustM.ok v)
    (i : Nat) (hi : i < v.val.size)
    (his : i < s.val.size) (hig : i < g.val.size) :
    (v.val[i]'hi).toInt =
      ((s.val[i]'his).toInt - (g.val[i]'hig).toInt).natAbs := by
  sorry

end Clever_150_compareObligations
