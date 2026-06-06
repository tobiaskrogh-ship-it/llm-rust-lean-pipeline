-- Companion obligations file for the `then_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import then_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Then_u64Obligations

/-- Postcondition (false branch): when `b = false`, `then_some` returns `None`,
    independent of what the closure `f` would have produced. This also captures
    the laziness property tested by `then_lazy`: the closure is never invoked
    in this branch, since the result does not depend on `f` at all.
    Covers the property tests `then_false_is_none_regardless_of_closure_value`
    and the false-branch assertion of the `then_basic` doc-test. -/
theorem then_false_is_none_regardless_of_closure_value
    (f : rust_primitives.hax.Tuple0 → RustM u64) :
    then_u64.then_some (rust_primitives.hax.Tuple0 → RustM u64) false f
      = pure core_models.option.Option.None := by
  rfl

/-- Postcondition (true branch): when `b = true`, `then_some` returns
    `Some v`, where `v` is the value the closure produces. The hypothesis
    `hf` captures the "closure produces `v`" semantics for the concrete
    closure representation `Tuple0 → RustM u64` (the `FnOnce.call_once`
    instance on this type just applies `f` to its argument).
    Covers the property test `then_true_passes_through_closure_value`
    and the true-branch assertion of the `then_basic` doc-test. -/
theorem then_true_passes_through_closure_value
    (f : rust_primitives.hax.Tuple0 → RustM u64) (v : u64)
    (hf : f rust_primitives.hax.Tuple0.mk = pure v) :
    then_u64.then_some (rust_primitives.hax.Tuple0 → RustM u64) true f
      = pure (core_models.option.Option.Some v) := by
  -- With `b = true`, the body reduces to `do let x ← f Tuple0.mk; pure (Some x)`
  -- since the `FnOnce` instance for `Tuple0 → RustM u64` defines
  -- `call_once f x := f x`. Substituting `hf` and using `pure_bind` closes it.
  show (do let x ← f rust_primitives.hax.Tuple0.mk
           pure (core_models.option.Option.Some x))
        = pure (core_models.option.Option.Some v)
  rw [hf]
  rfl

end Then_u64Obligations
