-- Companion obligations file for the `map_len_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_len_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_len_u64Obligations

open map_len_u64
open core_models.ops.range

/-- Postcondition (well-formed range): when the inner `Range` satisfies
    `start ≤ _end`, `Impl.len self` returns `(_end - start) as usize`.

    Captures the property test
    `len_equals_end_minus_start_for_wellformed_ranges`: for any well-formed
    `Range<u64>` (`start ≤ end`), `Map::len()` agrees with the documented
    formula `(end - start) as usize`. The precondition `start ≤ _end`
    discharges the underflow branch of the `-?` operator; the subsequent
    `cast_op : u64 → usize` is the unsigned widening `UInt64.toUSize64`,
    which on a 64-bit target is exact (`usize` is `USize64`, a copy of
    `UInt64`). A buggy implementation that swapped operands, off-by-one'd,
    or returned a sentinel value would falsify this. -/
theorem Impl_len_postcondition (self : Map)
    (h : (Map.iter self).start ≤ (Map.iter self)._end) :
    Impl.len self = RustM.ok (UInt64.toUSize64
      ((Map.iter self)._end - (Map.iter self).start)) := by
  sorry

/-- Failure mode (ill-formed range): when the inner `Range` satisfies
    `_end < start`, the partial subtraction `-?` underflows and the
    function fails with `.integerOverflow`.

    Not directly tested in the Rust source (the documented precondition
    forbids `end < start`), but pins down the model's behaviour on the
    out-of-precondition branch — analogous to the `out_of_bounds_returns_*`
    theorems in the slice-indexing references. A buggy implementation that
    let the underflow through (e.g. via `wrapping_sub`) would falsify this. -/
theorem Impl_len_underflow (self : Map)
    (h : (Map.iter self)._end < (Map.iter self).start) :
    Impl.len self = RustM.fail .integerOverflow := by
  sorry

/-- Totality (under the precondition): for every well-formed `Map`,
    `Impl.len self` returns some `usize` successfully. Follows from the
    postcondition; stated separately as the explicit "no panic on
    well-formed input" clause that matches the Rust contract's
    `precondition: start ≤ end` half. -/
theorem Impl_len_total (self : Map)
    (h : (Map.iter self).start ≤ (Map.iter self)._end) :
    ∃ v : usize, Impl.len self = RustM.ok v :=
  ⟨UInt64.toUSize64 ((Map.iter self)._end - (Map.iter self).start),
   Impl_len_postcondition self h⟩

/-- Independence of `f`: the value of `len` does not depend on the closure
    field `f` of the `Map` — only on the inner `iter` range.

    Captures the property test `len_is_independent_of_f`: a buggy
    implementation that consulted `f` (called it on the endpoints, hashed
    the function pointer, ...) would be caught by this. In the Lean
    extraction, `Impl.len` is defined without mentioning `Map.f`, so the
    statement holds by definitional unfolding. -/
theorem Impl_len_independent_of_f
    (r : core_models.ops.range.Range u64) (f g : u64 → RustM u64) :
    Impl.len ⟨r, f⟩ = Impl.len ⟨r, g⟩ := by
  sorry

end Map_len_u64Obligations
