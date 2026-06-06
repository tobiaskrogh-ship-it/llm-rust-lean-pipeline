
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


namespace map_len_u64

--  Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
structure Map where
  iter : (core_models.ops.range.Range u64)
  f : (u64 -> RustM u64)

--  Return the remaining length, delegating to the inner iterator's `len`
--  (inlined as `end - start` for `Range<u64>`).
@[spec]
def Impl.len (self : Map) : RustM usize := do
  (rust_primitives.hax.cast_op
    (← ((core_models.ops.range.Range._end (Map.iter self))
      -? (core_models.ops.range.Range.start (Map.iter self)))) :
    RustM usize)

end map_len_u64

