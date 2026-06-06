
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


namespace clever_035_fizz_buzz

--  Count occurrences of the digit 7 across integers strictly less than n
--  that are divisible by 11 or 13.
@[spec]
def count_sevens (n : i64) : RustM i64 := do
  if (← (n <=? (0 : i64))) then do
    (pure (0 : i64))
  else do
    if (← ((← (n %? (10 : i64))) ==? (7 : i64))) then do
      ((← (count_sevens (← (n /? (10 : i64))))) +? (1 : i64))
    else do
      (count_sevens (← (n /? (10 : i64))))
partial_fixpoint

@[spec]
def scan_at (i : i64) (n : i64) (acc : i64) : RustM i64 := do
  if (← (i >=? n)) then do
    (pure acc)
  else do
    if
    (← ((← ((← (i %? (11 : i64))) ==? (0 : i64)))
      ||? (← ((← (i %? (13 : i64))) ==? (0 : i64))))) then do
      (scan_at (← (i +? (1 : i64))) n (← (acc +? (← (count_sevens i)))))
    else do
      (scan_at (← (i +? (1 : i64))) n acc)
partial_fixpoint

@[spec]
def fizz_buzz (n : i64) : RustM i64 := do (scan_at (0 : i64) n (0 : i64))

end clever_035_fizz_buzz

