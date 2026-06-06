-- Companion obligations file for the `count_to` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import count_to

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Count_toObligations

/-- Postcondition (functional correctness / identity).

The Rust source defines `count_to(n)` as the recursion
`if n == 0 then 0 else count_to(n - 1) + 1`, which mathematically
equals `n`. We state the universal identity directly:
`count_to n` succeeds and returns `n` for every `u64` input.

No precondition is needed: the subtraction `n - 1` is guarded by
the explicit `n == 0` branch (no underflow), and the final
addition `(n - 1) + 1 = n` fits in `u64` because `n` itself is a
`u64` (no overflow).

This single clause subsumes both the dense `0..=100` sweep
(`counts_to_n`) and the wider deterministic sample up to 10_000
(`count_to_is_identity_on_wider_sample`) in the Rust tests. -/
theorem count_to_identity (n : u64) :
    count_to.count_to n = RustM.ok n := by
  sorry

/-- Postcondition (boundary anchor): `count_to(0)` returns `0`.

This is the explicit boundary test `count_to_zero_is_zero` from
the Rust source. It is a corollary of `count_to_identity` at
`n = 0`, but we keep it as an independent theorem so the base
case of the recursion is pinned down explicitly. -/
theorem count_to_zero :
    count_to.count_to 0 = RustM.ok 0 := by
  sorry

end Count_toObligations
