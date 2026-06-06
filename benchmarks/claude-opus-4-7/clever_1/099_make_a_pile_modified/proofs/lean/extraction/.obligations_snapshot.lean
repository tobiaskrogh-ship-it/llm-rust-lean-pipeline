-- Companion obligations file for the `clever_099_make_a_pile` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_099_make_a_pile

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_099_make_a_pileObligations

/-!
The Rust source contains two contract-style property tests:

  * `length_is_n`       — postcondition (length): the returned `Vec`
                          has exactly `n` elements.
  * `element_formula`   — postcondition (contents): the element at
                          index `k` is `n + 2 * k` for every `k < n`.

Together these pin down the full specification of `make_a_pile`.

Note on the precondition. The proptest bounds `n ∈ [0, 1000)`, but the
Lean model permits any `u64`. For values of `n` near `u64::MAX`, the
inner recursion computes `2 *? k` for `k` up to `n − 1` (overflows if
`2 * (n − 1) ≥ 2^64`) and `n +? (2 * k)` whose worst case is
`n + 2 * (n − 1) = 3n − 2` (overflows if `3n − 2 ≥ 2^64`). The
strongest common precondition that prevents both overflows uniformly is
`3 * n.toNat ≤ USize64.size` (i.e. `≤ 2^64`):

  * for `n ≥ 1`, it yields `2 * (n − 1) ≤ 2 * n − 2 < 3n ≤ 2^64` and
    `3n − 2 < 2^64`;
  * for `n = 0`, the recursion is skipped entirely, so the bound is
    vacuously safe.

This is strictly weaker than the proptest's `n < 1000` and matches the
"safe arithmetic" idiom used by the existing references (e.g. the
`2 * s.val.size ≤ USize64.size` bound in `intersperse_modified`).
-/

/-- Length clause: the returned `Vec` has exactly `n` elements.
    Captures the Rust property test `length_is_n`. -/
theorem make_a_pile_length (n : u64) :
    ⦃ ⌜ 3 * n.toNat ≤ USize64.size ⌝ ⦄
    clever_099_make_a_pile.make_a_pile n
    ⦃ ⇓ r => ⌜ r.val.size = n.toNat ⌝ ⦄ := by
  sorry

/-- Per-index formula: the element at position `k` equals `n + 2 * k`.
    Captures the Rust property test `element_formula`. -/
theorem make_a_pile_element_formula (n : u64) :
    ⦃ ⌜ 3 * n.toNat ≤ USize64.size ⌝ ⦄
    clever_099_make_a_pile.make_a_pile n
    ⦃ ⇓ r => ⌜ ∀ (k : Nat) (hk : k < r.val.size),
                  (r.val[k]'hk).toNat = n.toNat + 2 * k ⌝ ⦄ := by
  sorry

end Clever_099_make_a_pileObligations
