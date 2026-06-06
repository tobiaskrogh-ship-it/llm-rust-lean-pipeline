
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


namespace apply_twice

@[spec]
def apply_twice
    (T : Type)
    [trait_constr_apply_twice_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_apply_twice_i0 : core_models.marker.Copy T ]
    (x : T)
    (f : (T -> RustM T)) :
    RustM T := do
  (f (← (f x)))

end apply_twice

