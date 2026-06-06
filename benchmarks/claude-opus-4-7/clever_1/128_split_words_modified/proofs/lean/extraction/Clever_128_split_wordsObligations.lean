-- Companion obligations file for the `clever_128_split_words` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_128_split_words

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_128_split_wordsObligations

-- Postcondition: split_words is the identity on i64.
-- (No precondition: the function is total on all i64 inputs.)
-- (No failure condition: the body is `pure txt`, which never fails.)
theorem split_words_spec (txt : i64) :
    clever_128_split_words.split_words txt = RustM.ok txt := rfl

end Clever_128_split_wordsObligations
