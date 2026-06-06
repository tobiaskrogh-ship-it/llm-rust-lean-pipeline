
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


namespace clever_145_get_max_triples

--  HumanEval/147 / CLEVER 145 — `get_max_triples(n)`.  Build the array
--  `a` of length `n` with `a[i] = (i+1)² - (i+1) + 1`.  Count triples
--  (i, j, k) with `i < j < k` such that `a[i] + a[j] + a[k]` is a
--  multiple of 3.  `n == 0` → 0.
@[spec]
def ai (i : u64) : RustM u64 := do
  let x : u64 ← (i +? (1 : u64));
  ((← ((← (x *? x)) -? x)) +? (1 : u64))

@[spec]
def loop_k (n : u64) (i : u64) (j : u64) (k : u64) (acc : u64) : RustM u64 := do
  if (← (k >? n)) then do
    (pure acc)
  else do
    if
    (← ((← ((← ((← ((← (ai (← (i -? (1 : u64)))))
            +? (← (ai (← (j -? (1 : u64)))))))
          +? (← (ai (← (k -? (1 : u64)))))))
        %? (3 : u64)))
      ==? (0 : u64))) then do
      (loop_k n i j (← (k +? (1 : u64))) (← (acc +? (1 : u64))))
    else do
      (loop_k n i j (← (k +? (1 : u64))) acc)
partial_fixpoint

@[spec]
def loop_j (n : u64) (i : u64) (j : u64) (acc : u64) : RustM u64 := do
  if (← (j >=? n)) then do
    (pure acc)
  else do
    (loop_j
      n
      i
      (← (j +? (1 : u64)))
      (← (loop_k n i j (← (j +? (1 : u64))) acc)))
partial_fixpoint

@[spec]
def loop_i (n : u64) (i : u64) (acc : u64) : RustM u64 := do
  if (← ((← (i +? (1 : u64))) >=? n)) then do
    (pure acc)
  else do
    (loop_i n (← (i +? (1 : u64))) (← (loop_j n i (← (i +? (1 : u64))) acc)))
partial_fixpoint

@[spec]
def get_max_triples (n : u64) : RustM u64 := do
  if (← (n <? (3 : u64))) then do
    (pure (0 : u64))
  else do
    (loop_i n (1 : u64) (0 : u64))

end clever_145_get_max_triples

