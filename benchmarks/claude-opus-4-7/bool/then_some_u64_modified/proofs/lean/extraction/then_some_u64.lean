
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


namespace then_some_u64

--  Returns `Some(t)` if `b` is `true`, or `None` otherwise.
-- 
--  Arguments passed to `then_some` are eagerly evaluated; if you are
--  passing the result of a function call, it is recommended to use
--  `then`, which is lazily evaluated.
@[spec]
def then_some (b : Bool) (t : u64) : RustM (core_models.option.Option u64) := do
  if b then do
    (pure (core_models.option.Option.Some t))
  else do
    (pure core_models.option.Option.None)

end then_some_u64

