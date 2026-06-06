-- Companion obligations file for the `map_rfold_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_rfold_u64

open Std.Do
open Std.Tactic
open map_rfold_u64
open core_models.ops.range

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_rfold_u64Obligations

/-- Reference specification of `Map.rfold`: the recursive right-to-left
    fold of the range `[start, _end)`, applying `f` to each element and
    combining the result with the accumulator via `g`. Mirrors the body
    of the Rust loop step-for-step (`acc := g(acc, f(end))` with `end`
    decreasing from `_end - 1` down to `start`).

    `n` is the iteration count (intended to be called with
    `n = self.iter._end.toNat - self.iter.start.toNat`). The partiality
    of `f` and `g` is preserved: a failure in either propagates up. -/
def rfoldSpec (n : Nat) (init : u64) (_end : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64) : RustM u64 :=
  match n with
  | 0 => RustM.ok init
  | n + 1 =>
      f (_end - 1) >>= fun v =>
        g init v >>= fun acc =>
          rfoldSpec n acc (_end - 1) f g

/-- Empty-range clause: when `self.iter._end ≤ self.iter.start`, the loop
    body never executes, so `Map.rfold` returns `init` without invoking
    either closure (in particular, it succeeds even for closures that
    would panic on every input).

    Captures `empty_range_returns_init_without_calling_closures`: for
    every `init` and every `self` whose range is empty (including the
    `u64::MAX..u64::MAX` boundary and the inverted-range case), the
    result is exactly `init` and the closures are never called. -/
theorem rfold_empty_range_returns_init
    (self : Map) (init : u64) (g : u64 → u64 → RustM u64)
    (h : self.iter._end ≤ self.iter.start) :
    Impl.rfold self init g = RustM.ok init := by
  sorry

/-- Main postcondition: `Map.rfold` agrees with the recursive reference
    spec `rfoldSpec`. The equation is stated unconditionally — both
    sides execute the same effects in the same order, so failures of
    `self.f` or `g` are mirrored on both sides.

    Captures `matches_iter_rfold_specification`: combining
    (a) `f` is applied to every element before `g` sees it, and
    (b) elements are folded right-to-left.

    The shifted-range identity (`rfold_matches_shifted_rfold`) and the
    fold/rfold agreement for an associative-commutative operation
    (`rfold_equals_fold_for_addition`) follow from this main equation
    plus algebraic facts; they are derived mathematical consequences
    rather than independent contract clauses and are intentionally not
    re-stated as separate theorems. -/
theorem rfold_matches_spec
    (self : Map) (init : u64) (g : u64 → u64 → RustM u64) :
    Impl.rfold self init g =
      rfoldSpec (self.iter._end.toNat - self.iter.start.toNat)
        init self.iter._end self.f g := by
  sorry

/-- Totality / no-panic: when both higher-order parameters always return
    successfully, `Map.rfold` also returns successfully. The only
    failure mode in the body is propagation of a closure failure — the
    `_end -? 1` step is guarded by `_end > start`, so it cannot
    underflow.

    The property tests use only total closures and never check for
    absence of panic explicitly, but a `Map.rfold` that panicked on
    some loop iteration would fail every one of them. We make the
    totality content explicit here. The `∀ x` hypotheses on `self.f`
    and `g` are necessary because the Lean model permits failing
    closures, even though the Rust source allows only `fn(...) -> u64`
    typed function pointers. -/
theorem rfold_total
    (self : Map) (init : u64) (g : u64 → u64 → RustM u64)
    (h_f : ∀ x : u64, ∃ y : u64, self.f x = RustM.ok y)
    (h_g : ∀ a b : u64, ∃ c : u64, g a b = RustM.ok c) :
    ∃ r : u64, Impl.rfold self init g = RustM.ok r := by
  sorry

end Map_rfold_u64Obligations
