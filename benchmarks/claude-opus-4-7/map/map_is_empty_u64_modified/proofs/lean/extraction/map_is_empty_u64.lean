
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace map_is_empty_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Report whether the inner iterator is empty.
@[spec]
def Impl.is_empty (self : Map) : RustM Bool := do
  ((core_models.ops.range.Range.start (Map.iter self))
    >=? (core_models.ops.range.Range._end (Map.iter self)))

end map_is_empty_u64

