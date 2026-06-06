-- Companion obligations file for the `map_size_hint_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_size_hint_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_size_hint_u64Obligations

open map_size_hint_u64
open core_models.ops.range
open core_models.option

/-- Postcondition (empty range): when `iter.start ≥ iter._end`, `size_hint`
    returns `(0, Some 0)` — the "empty range" branch.

    Captures `size_hint_empty_range_is_zero_exact` (start == end) and
    `size_hint_reversed_range_is_zero_exact` (start > end). The branch
    guard `start >= end` makes the entire `else` arithmetic unreachable, so
    no overflow/cast obligations are needed on this branch. -/
theorem size_hint_empty
    (self : Map)
    (h : self.iter._end ≤ self.iter.start) :
    Impl.size_hint self =
      RustM.ok (rust_primitives.hax.Tuple2.mk
                  (0 : usize) (Option.Some (0 : usize))) := by
  sorry

/-- Postcondition (non-empty range): when `iter.start < iter._end`, `size_hint`
    returns `(n, Some n)` where `n` is `end - start` cast to `usize`.

    Captures `size_hint_passes_through_full_range`,
    `size_hint_passes_through_after_partial_consumption`,
    `size_hint_passes_through_after_back_consumption`, and the non-empty
    cases of `size_hint_matches_inner_for_various_ranges`. The `start < end`
    precondition makes the partial subtraction `end -? start` safe: from
    `start < end` (both `u64`) we get `start.toNat < end.toNat`, hence
    `usubOverflow` is false. On 64-bit targets (the Lean model), the
    `u64 → usize` cast is `UInt64.toUSize64`, which is lossless and total,
    so the `cast_op` step also succeeds. -/
theorem size_hint_nonempty
    (self : Map)
    (h : self.iter.start < self.iter._end) :
    Impl.size_hint self =
      RustM.ok (rust_primitives.hax.Tuple2.mk
                  (UInt64.toUSize64 (self.iter._end - self.iter.start))
                  (Option.Some
                    (UInt64.toUSize64 (self.iter._end - self.iter.start)))) := by
  sorry

/-- Independence of `f`: two `Map`s with the same `iter` but possibly
    different mapper closures return the same `size_hint`.

    Captures `size_hint_is_independent_of_f`. The function body never
    mentions `self.f`, so this is an independent contract clause about the
    *shape* of the spec, not a derived fact about its value: a buggy
    implementation that consulted `f` (e.g., to filter elements) would
    break this clause without necessarily breaking pass-through. -/
theorem size_hint_independent_of_f
    (iter : Range u64) (f g : u64 → RustM u64) :
    Impl.size_hint { iter := iter, f := f }
      = Impl.size_hint { iter := iter, f := g } := by
  sorry

/-- Totality / no-panic: for every `Map`, `size_hint` returns successfully.

    The branch on `start >= end` makes the partial subtraction in the
    non-empty branch safe (the guard `start < end` implies no underflow),
    and the `u64 → usize` cast is total on the 64-bit Lean model. The
    `then` branch is a pure `pure (…)` with no failure mode. So there is
    no input on which the function panics — this matches the test suite
    having no `should_panic` test. -/
theorem size_hint_total (self : Map) :
    ∃ r, Impl.size_hint self = RustM.ok r := by
  sorry

end Map_size_hint_u64Obligations
