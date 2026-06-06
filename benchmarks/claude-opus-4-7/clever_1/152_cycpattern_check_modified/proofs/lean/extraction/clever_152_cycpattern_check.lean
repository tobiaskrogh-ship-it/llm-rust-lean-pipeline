
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


namespace clever_152_cycpattern_check

--  CLEVER 152 — `cycpattern_check(a, b)`.  The canonical CLEVER
--  signature is `pub fn cycpattern_check(String a: i64, String b: i64)
--  -> bool`, which is syntactically broken Rust (mixes `String` and
--  `i64`).  The HumanEval problem is string-based (test whether any
--  rotation of `b` is a substring of `a`); no faithful integer
--  adaptation exists.  Returning `false` as a degenerate stub;
--  flagged upstream in CLEVER's prompt set.
@[spec]
def cycpattern_check (a : i64) (b : i64) : RustM Bool := do
  let _ := a;
  let _ := b;
  (pure false)

end clever_152_cycpattern_check

