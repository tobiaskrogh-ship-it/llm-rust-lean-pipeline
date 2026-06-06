-- Companion obligations file for the `map_next_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_next_u64

open Std.Do
open Std.Tactic
open map_next_u64
open core_models.ops.range
open core_models.option

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_next_u64Obligations

/-- Postcondition (empty range): when `iter.start ≥ iter._end`, `Impl.next`
    returns `None` and leaves the inner range and mapper untouched.

    Captures `prop_empty_range_yields_none_and_is_noop`: every empty
    range (including the boundary `start == end` cases at `u64::MAX` and
    the inverted `start > end` cases) yields `None`, and the inner
    `iter.start` / `iter._end` are unchanged. The "calling again still
    yields None" tail of that property test is the same statement applied
    a second time to the (unchanged) self, so no separate theorem is
    needed for stability of the exhausted state. -/
theorem next_empty_returns_none
    (self : Map)
    (h : self.iter._end ≤ self.iter.start) :
    Impl.next self =
      RustM.ok (rust_primitives.hax.Tuple2.mk self Option.None) := by
  sorry

/-- Postcondition (non-empty range): when `iter.start < iter._end` and the
    mapper `self.f` succeeds on the current `iter.start` with value `r`,
    `Impl.next` returns `Some r` and advances `iter.start` by exactly one,
    leaving `iter._end` and `self.f` unchanged.

    Captures `prop_nonempty_yields_some_f_start_and_advances_by_one`:
    `m.next() == Some(f(start)) ∧ m.iter.start == start + 1 ∧ m.iter.end == end`
    whenever `start < end`. The `start < end` precondition also rules out
    overflow in the `start +? 1` step (since `start ≤ end - 1 ≤ u64::MAX - 1`),
    so no separate overflow-failure obligation is needed on this branch. -/
theorem next_nonempty_returns_some_mapped
    (self : Map) (r : u64)
    (h_lt : self.iter.start < self.iter._end)
    (h_f  : self.f self.iter.start = RustM.ok r) :
    Impl.next self =
      RustM.ok (rust_primitives.hax.Tuple2.mk
        { self with iter := { self.iter with start := self.iter.start + 1 } }
        (Option.Some r)) := by
  sorry

/-- Totality / no-panic: given that the mapper succeeds on the value it
    will be called with (i.e. on `iter.start` when the range is non-empty),
    `Impl.next` returns successfully — it never panics on overflow. The
    `+?` operator in the function body cannot overflow because
    `start < end ≤ u64::MAX` implies `start + 1 ≤ u64::MAX`, and the
    empty-range branch carries no failure mode at all. The mapper-totality
    hypothesis is necessary because `self.f : u64 → RustM u64` is an
    arbitrary higher-order field; the property tests use only total
    mappers, but the model permits failing ones. -/
theorem next_total
    (self : Map)
    (h_f : self.iter.start < self.iter._end →
           ∃ r : u64, self.f self.iter.start = RustM.ok r) :
    ∃ result, Impl.next self = RustM.ok result := by
  sorry

end Map_next_u64Obligations
