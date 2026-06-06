-- Companion obligations file for the `map_fold_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_fold_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_fold_u64Obligations

-- Smoke obligation: probe whether the upstream `import map_fold_u64`
-- typechecks at all. If even this trivial theorem fails to build, the
-- failure is upstream in the Hax-extracted module.
theorem import_smoke : True := trivial

end Map_fold_u64Obligations
