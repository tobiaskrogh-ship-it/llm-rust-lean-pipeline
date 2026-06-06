-- Companion obligations file for the `ok_or_else_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import ok_or_else_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Ok_or_else_u64Obligations

/-- Postcondition (success branch).
    When `b = true`, `ok_or_else` returns `Ok(())` — independently of the closure.
    Captures the Rust property test
    `true_branch_returns_ok_regardless_of_closure_value`. -/
theorem ok_or_else_true_returns_ok
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
        F rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 :
      core_models.ops.function.FnOnce F rust_primitives.hax.Tuple0
        (associatedTypes := {
          show core_models.ops.function.FnOnce.AssociatedTypes
            F rust_primitives.hax.Tuple0
          by infer_instance
          with Output := u64})]
    (f : F) :
    ok_or_else_u64.ok_or_else F true f =
      pure (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk) :=
  rfl

/-- Postcondition (failure branch).
    When `b = false`, `ok_or_else` forwards the closure's return value verbatim
    inside `Err` — no clamping, transformation, or substitution. Captures the
    Rust property test `false_branch_forwards_closure_value_verbatim`. -/
theorem ok_or_else_false_forwards_closure
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
        F rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 :
      core_models.ops.function.FnOnce F rust_primitives.hax.Tuple0
        (associatedTypes := {
          show core_models.ops.function.FnOnce.AssociatedTypes
            F rust_primitives.hax.Tuple0
          by infer_instance
          with Output := u64})]
    (f : F) :
    ok_or_else_u64.ok_or_else F false f =
      (do
        let v ← core_models.ops.function.FnOnce.call_once
                  F rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk
        pure (core_models.result.Result.Err v)) :=
  rfl

/-- Closure-call semantics (zero-invocation half).
    On the `true` branch the result is identical for any two closures, so the
    closure cannot have been invoked. Captures the `count_true == 0` half of
    the Rust property test `closure_called_exactly_once_iff_false` (the
    `count_false == 1` half is captured structurally by
    `ok_or_else_false_forwards_closure`, whose RHS contains exactly one bind
    on `call_once`). -/
theorem ok_or_else_true_independent_of_closure
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
        F rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 :
      core_models.ops.function.FnOnce F rust_primitives.hax.Tuple0
        (associatedTypes := {
          show core_models.ops.function.FnOnce.AssociatedTypes
            F rust_primitives.hax.Tuple0
          by infer_instance
          with Output := u64})]
    (f1 f2 : F) :
    ok_or_else_u64.ok_or_else F true f1 = ok_or_else_u64.ok_or_else F true f2 :=
  rfl

end Ok_or_else_u64Obligations
