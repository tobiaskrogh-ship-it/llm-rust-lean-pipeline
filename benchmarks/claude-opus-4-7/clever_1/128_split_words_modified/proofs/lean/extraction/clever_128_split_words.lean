
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


namespace clever_128_split_words

--  CLEVER 128 — `split_words(txt)`.  The canonical CLEVER signature is
--  `pub fn split_words(txt: i64) -> i64`, which has no relationship to
--  the HumanEval/128 string-splitting problem.  No faithful integer
--  implementation exists; returning `txt` unchanged as a degenerate
--  stub.  Flagged upstream in CLEVER's prompt set.
@[spec]
def split_words (txt : i64) : RustM i64 := do (pure txt)

end clever_128_split_words

