-- Companion obligations file for the `apply_twice` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import apply_twice

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Apply_twiceObligations

/-- Postcondition: `apply_twice x f` equals `f(f(x))`.

    In the Rust source the function signature is `fn(T, fn(T) -> T) -> T` and
    the body is the pure expression `f(f(x))`. Hax extracts the (potentially
    panicking) function `f` as `T -> RustM T`, so the Rust expression
    `f(f(x))` becomes the monadic composition `f x >>= f`, equivalently
    `do let y ← f x; f y`.

    This single equation captures the entire contract:
      * No precondition — the function is total on every `(x, f)`.
      * No failure mode of its own — `apply_twice` itself does no arithmetic,
        indexing, or partial operation; any failure comes purely from `f`,
        and is faithfully propagated by the bind.
      * Postcondition — the output is exactly `f(f(x))`.

    Both Rust property tests
      * `returns_f_applied_twice_additive`        (f = λn, n+1, over i64)
      * `returns_f_applied_twice_multiplicative`  (f = λn, n*3, over i32)
    instantiate this single contract with different choices of `f`, and
    are subsumed by the universal statement below. -/
theorem apply_twice_spec
    (T : Type)
    [trait_constr_apply_twice_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes T]
    [trait_constr_apply_twice_i0 : core_models.marker.Copy T]
    (x : T) (f : T -> RustM T) :
    apply_twice.apply_twice T x f = f x >>= f := rfl

end Apply_twiceObligations
