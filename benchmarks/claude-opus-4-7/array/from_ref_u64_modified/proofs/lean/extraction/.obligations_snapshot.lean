-- Companion obligations file for the `from_ref_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import from_ref_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace From_ref_u64Obligations

open from_ref_u64

/-- Postcondition (element equality): `from_ref s` returns a length-1 array
    whose sole element equals the input `s`.

    Captures the Rust property test `prop_element_equals_input`
    (and the corresponding clause of `array_from_ref`):
    `from_ref(&x)[0] == x` for every `u64` input. A buggy implementation
    that returned a fresh default, a shifted/masked value, or any other
    `u64` distinct from `s` would falsify this.

    NOTE: Hax extracted the body of `from_ref` as `pure sorry` (the
    `unsafe` pointer cast has no Lean translation), so the array value
    is the opaque `sorry`. This statement is therefore well-typed but
    cannot be proved without further axioms — the proof stage will
    necessarily exit with `sorry`. -/
theorem from_ref_element_equals_input (s : u64) :
    from_ref s = RustM.ok (RustArray.ofVec #v[s]) := by
  sorry

/-- Totality / no-panic: for every `u64` input, `from_ref` returns
    successfully (no panic, no overflow, no out-of-bounds error).

    `from_ref` is a `const fn` performing a single (in Rust) `unsafe`
    pointer reinterpretation with no fallible operation; in the
    extracted model it is `pure sorry`, which is structurally
    `RustM.ok _`. A buggy implementation that introduced a fallible
    step (e.g. a checked indexing on the resulting array before
    returning it) would falsify this. -/
theorem from_ref_total (s : u64) :
    ∃ v : RustArray u64 1, from_ref s = RustM.ok v := by
  sorry

end From_ref_u64Obligations
