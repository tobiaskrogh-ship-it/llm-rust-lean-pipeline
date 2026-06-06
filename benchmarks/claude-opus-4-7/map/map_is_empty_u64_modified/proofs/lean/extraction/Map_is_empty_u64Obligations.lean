-- Companion obligations file for the `map_is_empty_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_is_empty_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_is_empty_u64Obligations

open map_is_empty_u64

/-- Postcondition (functional spec): `is_empty` returns `ok` of the Boolean
    `start >= end` predicate over the inner `Range`. No precondition (the
    function is total) and no failure case (the comparison cannot panic). -/
theorem is_empty_spec (self : Map) :
    Impl.is_empty self =
      RustM.ok (decide (self.iter.start ≥ self.iter._end)) := rfl

/-- Postcondition (interface): the result does not depend on the mapping
    function `f`. Swapping `f` for any other `u64 -> RustM u64` while keeping
    the inner `Range` fixed yields the same answer. -/
theorem is_empty_independent_of_mapper
    (iter : core_models.ops.range.Range u64) (f g : u64 -> RustM u64) :
    Impl.is_empty ⟨iter, f⟩ = Impl.is_empty ⟨iter, g⟩ := rfl

end Map_is_empty_u64Obligations
