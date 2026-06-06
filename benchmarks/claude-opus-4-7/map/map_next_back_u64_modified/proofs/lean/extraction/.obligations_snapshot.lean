-- Companion obligations file for the `map_next_back_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_next_back_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_next_back_u64Obligations

open map_next_back_u64
open core_models.ops.range
open core_models.option
open rust_primitives.hax

/-- Empty-range clause: when `self.iter.start ≥ self.iter._end`, `next_back`
    returns `(self, None)` unchanged — no mutation, no invocation of `f`,
    no failure.

    Captures the property test `prop_empty_range_returns_none_and_preserves_iter`:
    for every empty range (including the canonical `start == end` case and the
    already-exhausted `end < start` case), the call yields `None` and leaves
    `iter.start` and `iter._end` exactly as they were. A buggy implementation
    that returned `Some _` on an empty range, mutated `iter` on the empty path,
    or invoked `f` would falsify this.

    The empty boundary case from `prop_contract_holds_at_u64_max_boundary`
    (range `u64::MAX..u64::MAX`) is a specialisation of this clause. -/
theorem next_back_empty (self : Map)
    (h : self.iter._end ≤ self.iter.start) :
    Impl.next_back self = RustM.ok (Tuple2.mk self Option.None) := by
  sorry

/-- Non-empty-range clause: when `self.iter.start < self.iter._end`, the call
    decrements `self.iter._end` by exactly one and returns
    `Some (f (self.iter._end - 1))` in the second tuple component, with
    `self.iter.start` left untouched. The result is threaded through the bind
    on `(Map.f self) (self.iter._end - 1)` so the equation holds regardless
    of whether `f` succeeds or fails on that argument.

    Captures the property test `prop_nonempty_range_pops_and_maps_back_element`
    (which asserts `r = Some (probe_fn (end - 1))`, `iter.start` unchanged,
    `iter._end = end - 1`) and the non-empty boundary case from
    `prop_contract_holds_at_u64_max_boundary`. The example tests
    `next_back_yields_last_mapped_item` and `next_back_after_partial_drain`
    are concrete instances of this clause. Because `self.iter._end > self.iter.start ≥ 0`
    forces `self.iter._end ≥ 1`, the partial `-?` operator in the extracted
    body cannot underflow, so the subtraction is safe and the equation can be
    rewritten to use ordinary `-` on the right-hand side. -/
theorem next_back_nonempty (self : Map)
    (h : self.iter.start < self.iter._end) :
    Impl.next_back self =
      (do
        let v ← (Map.f self) (self.iter._end - 1)
        pure (Tuple2.mk
                { self with iter := { self.iter with _end := self.iter._end - 1 } }
                (Option.Some v))) := by
  sorry

end Map_next_back_u64Obligations
