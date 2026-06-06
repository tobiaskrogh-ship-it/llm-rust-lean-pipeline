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
  unfold Impl.next_back
  simp only [rust_primitives.cmp.ge, bind_pure_comp, pure_bind]
  have hge : decide (self.iter._end ≤ self.iter.start) = true := by
    rw [decide_eq_true_iff]; exact h
  simp [hge]
  rfl

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
  unfold Impl.next_back
  simp only [rust_primitives.cmp.ge, bind_pure_comp, pure_bind,
             rust_primitives.ops.arith.Sub.sub]
  have hnge : decide (self.iter._end ≤ self.iter.start) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    have h1 : self.iter.start.toNat < self.iter._end.toNat :=
      UInt64.lt_iff_toNat_lt.mp h
    have h2 : self.iter._end.toNat ≤ self.iter.start.toNat :=
      UInt64.le_iff_toNat_le.mp hle
    omega
  have h_end_pos : (1 : UInt64).toNat ≤ self.iter._end.toNat := by
    have h1 : self.iter.start.toNat < self.iter._end.toNat :=
      UInt64.lt_iff_toNat_lt.mp h
    simp; omega
  have h_no_overflow : BitVec.usubOverflow self.iter._end.toBitVec (1#64) = false := by
    show UInt64.subOverflow self.iter._end (1 : UInt64) = false
    rw [Bool.eq_false_iff, ne_eq, UInt64.subOverflow_iff]
    omega
  simp [hnge, h_no_overflow]

end Map_next_back_u64Obligations
